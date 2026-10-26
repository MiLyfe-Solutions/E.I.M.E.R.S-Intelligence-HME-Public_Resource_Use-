import V185TrunkScan23Chunk0263

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1561615 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_1561615 : Nat := 118140960795 + 1561615 * 2 ^ 59
def prefixEnd_1561615 : Nat := 4983230072969 + 3 ^ 40 * 1561615 * 2
def baseEnd_1561615 : Nat := 801859092271012907830769

theorem tailTrace_1561615 : CollatzResearch.WordTrace tailWord_1561615 prefixEnd_1561615 801859092271012907830769 := by
  unfold tailWord_1561615
  simp only [CollatzResearch.WordTrace]
  refine ⟨56956778237543032453830299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37971185491695354969220199 56956778237543032453830299)
  ·
    refine ⟨85435167356314548680745449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56956778237543032453830299 85435167356314548680745449)
    ·
      refine ⟨64076375517235911510559087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85435167356314548680745449 64076375517235911510559087)
      ·
        refine ⟨96114563275853867265838631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64076375517235911510559087 96114563275853867265838631)
        ·
          refine ⟨144171844913780800898757947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96114563275853867265838631 144171844913780800898757947)
          ·
            refine ⟨216257767370671201348136921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144171844913780800898757947 216257767370671201348136921)
            ·
              refine ⟨162193325528003401011102691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216257767370671201348136921 162193325528003401011102691)
              ·
                refine ⟨243289988292005101516654037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162193325528003401011102691 243289988292005101516654037)
                ·
                  refine ⟨5702109100593869566796579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 243289988292005101516654037 5702109100593869566796579)
                  ·
                    refine ⟨8553163650890804350194869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702109100593869566796579 8553163650890804350194869)
                    ·
                      refine ⟨801859092271012907830769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8553163650890804350194869 801859092271012907830769)
                      ·
                        rfl

theorem cell23_1561615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_1561615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561615 prefixEnd_1561615 := by exact prefixLift 1561615
  have htrace : WordTrace (prefixWord ++ tailWord_1561615) baseStart_1561615 baseEnd_1561615 := by
    simpa [prefixWord, tailWord_1561615, baseEnd_1561615] using wordTrace_append hprefix tailTrace_1561615
  have hstable : (prefixWord ++ tailWord_1561615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561615).length < 2 ^ (prefixWord ++ tailWord_1561615).sum := by decide
  have hdescent : baseEnd_1561615 < baseStart_1561615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561623 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1561623 : Nat := 118140960795 + 1561623 * 2 ^ 59
def prefixEnd_1561623 : Nat := 4983230072969 + 3 ^ 40 * 1561623 * 2
def baseEnd_1561623 : Nat := 801863200116248876530733

theorem tailTrace_1561623 : CollatzResearch.WordTrace tailWord_1561623 prefixEnd_1561623 801863200116248876530733 := by
  unfold tailWord_1561623
  simp only [CollatzResearch.WordTrace]
  refine ⟨56957070021514049820121523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37971380014342699880081015 56957070021514049820121523)
  ·
    refine ⟨85435605032271074730182285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56957070021514049820121523 85435605032271074730182285)
    ·
      refine ⟨32038351887101653023818357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85435605032271074730182285 32038351887101653023818357)
      ·
        refine ⟨3003595489415779970982971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32038351887101653023818357 3003595489415779970982971)
        ·
          refine ⟨4505393234123669956474457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003595489415779970982971 4505393234123669956474457)
          ·
            refine ⟨3379044925592752467355843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505393234123669956474457 3379044925592752467355843)
            ·
              refine ⟨5068567388389128701033765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379044925592752467355843 5068567388389128701033765)
              ·
                refine ⟨950356385322961631443831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5068567388389128701033765 950356385322961631443831)
                ·
                  refine ⟨1425534577984442447165747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950356385322961631443831 1425534577984442447165747)
                  ·
                    refine ⟨2138301866976663670748621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1425534577984442447165747 2138301866976663670748621)
                    ·
                      refine ⟨801863200116248876530733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2138301866976663670748621 801863200116248876530733)
                      ·
                        rfl

theorem cell23_1561623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1561623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561623 prefixEnd_1561623 := by exact prefixLift 1561623
  have htrace : WordTrace (prefixWord ++ tailWord_1561623) baseStart_1561623 baseEnd_1561623 := by
    simpa [prefixWord, tailWord_1561623, baseEnd_1561623] using wordTrace_append hprefix tailTrace_1561623
  have hstable : (prefixWord ++ tailWord_1561623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561623).length < 2 ^ (prefixWord ++ tailWord_1561623).sum := by decide
  have hdescent : baseEnd_1561623 < baseStart_1561623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561625 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1561625 : Nat := 118140960795 + 1561625 * 2 ^ 59
def prefixEnd_1561625 : Nat := 4983230072969 + 3 ^ 40 * 1561625 * 2
def baseEnd_1561625 : Nat := 801864227077557868705723

theorem tailTrace_1561625 : CollatzResearch.WordTrace tailWord_1561625 prefixEnd_1561625 801864227077557868705723 := by
  unfold tailWord_1561625
  simp only [CollatzResearch.WordTrace]
  refine ⟨56957142967506804161694329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37971428645004536107796219 56957142967506804161694329)
  ·
    refine ⟨42717857225630103121270747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56957142967506804161694329 42717857225630103121270747)
    ·
      refine ⟨64076785838445154681906121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42717857225630103121270747 64076785838445154681906121)
      ·
        refine ⟨48057589378833866011429591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64076785838445154681906121 48057589378833866011429591)
        ·
          refine ⟨72086384068250799017144387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48057589378833866011429591 72086384068250799017144387)
          ·
            refine ⟨108129576102376198525716581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72086384068250799017144387 108129576102376198525716581)
            ·
              refine ⟨20274295519195537223571859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108129576102376198525716581 20274295519195537223571859)
              ·
                refine ⟨30411443278793305835357789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20274295519195537223571859 30411443278793305835357789)
                ·
                  refine ⟨11404291229547489688259171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30411443278793305835357789 11404291229547489688259171)
                  ·
                    refine ⟨17106436844321234532388757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11404291229547489688259171 17106436844321234532388757)
                    ·
                      refine ⟨801864227077557868705723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17106436844321234532388757 801864227077557868705723)
                      ·
                        rfl

theorem cell23_1561625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1561625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561625 prefixEnd_1561625 := by exact prefixLift 1561625
  have htrace : WordTrace (prefixWord ++ tailWord_1561625) baseStart_1561625 baseEnd_1561625 := by
    simpa [prefixWord, tailWord_1561625, baseEnd_1561625] using wordTrace_append hprefix tailTrace_1561625
  have hstable : (prefixWord ++ tailWord_1561625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561625).length < 2 ^ (prefixWord ++ tailWord_1561625).sum := by decide
  have hdescent : baseEnd_1561625 < baseStart_1561625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561639 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1561639 : Nat := 118140960795 + 1561639 * 2 ^ 59
def prefixEnd_1561639 : Nat := 4983230072969 + 3 ^ 40 * 1561639 * 2
def baseEnd_1561639 : Nat := 267290471935573604643553

theorem tailTrace_1561639 : CollatzResearch.WordTrace tailWord_1561639 prefixEnd_1561639 267290471935573604643553 := by
  unfold tailWord_1561639
  simp only [CollatzResearch.WordTrace]
  refine ⟨56957653589456084552703971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37971769059637389701802647 56957653589456084552703971)
  ·
    refine ⟨85436480384184126829055957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56957653589456084552703971 85436480384184126829055957)
    ·
      refine ⟨2002417509004315472555999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85436480384184126829055957 2002417509004315472555999)
      ·
        refine ⟨3003626263506473208833999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002417509004315472555999 3003626263506473208833999)
        ·
          refine ⟨4505439395259709813250999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003626263506473208833999 4505439395259709813250999)
          ·
            refine ⟨6758159092889564719876499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505439395259709813250999 6758159092889564719876499)
            ·
              refine ⟨10137238639334347079814749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758159092889564719876499 10137238639334347079814749)
              ·
                refine ⟨3801464489750380154930531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10137238639334347079814749 3801464489750380154930531)
                ·
                  refine ⟨5702196734625570232395797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801464489750380154930531 5702196734625570232395797)
                  ·
                    refine ⟨267290471935573604643553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5702196734625570232395797 267290471935573604643553)
                    ·
                      rfl

theorem cell23_1561639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1561639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561639 prefixEnd_1561639 := by exact prefixLift 1561639
  have htrace : WordTrace (prefixWord ++ tailWord_1561639) baseStart_1561639 baseEnd_1561639 := by
    simpa [prefixWord, tailWord_1561639, baseEnd_1561639] using wordTrace_append hprefix tailTrace_1561639
  have hstable : (prefixWord ++ tailWord_1561639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561639).length < 2 ^ (prefixWord ++ tailWord_1561639).sum := by decide
  have hdescent : baseEnd_1561639 < baseStart_1561639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561649 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_1561649 : Nat := 118140960795 + 1561649 * 2 ^ 59
def prefixEnd_1561649 : Nat := 4983230072969 + 3 ^ 40 * 1561649 * 2
def baseEnd_1561649 : Nat := 801876550613265774805613

theorem tailTrace_1561649 : CollatzResearch.WordTrace tailWord_1561649 prefixEnd_1561649 801876550613265774805613 := by
  unfold tailWord_1561649
  simp only [CollatzResearch.WordTrace]
  refine ⟨56958018319419856260568001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37972012212946570840378667 56958018319419856260568001)
  ·
    refine ⟨42718513739564892195426001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56958018319419856260568001 42718513739564892195426001)
    ·
      refine ⟨32038885304673669146569501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42718513739564892195426001 32038885304673669146569501)
      ·
        refine ⟨12014581989252625929963563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32038885304673669146569501 12014581989252625929963563)
        ·
          refine ⟨18021872983878938894945345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12014581989252625929963563 18021872983878938894945345)
          ·
            refine ⟨13516404737909204171209009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18021872983878938894945345 13516404737909204171209009)
            ·
              refine ⟨10137303553431903128406757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13516404737909204171209009 10137303553431903128406757)
              ·
                refine ⟨1900744416268481836576267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10137303553431903128406757 1900744416268481836576267)
                ·
                  refine ⟨2851116624402722754864401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900744416268481836576267 2851116624402722754864401)
                  ·
                    refine ⟨2138337468302042066148301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851116624402722754864401 2138337468302042066148301)
                    ·
                      refine ⟨801876550613265774805613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2138337468302042066148301 801876550613265774805613)
                      ·
                        rfl

theorem cell23_1561649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_1561649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561649 prefixEnd_1561649 := by exact prefixLift 1561649
  have htrace : WordTrace (prefixWord ++ tailWord_1561649) baseStart_1561649 baseEnd_1561649 := by
    simpa [prefixWord, tailWord_1561649, baseEnd_1561649] using wordTrace_append hprefix tailTrace_1561649
  have hstable : (prefixWord ++ tailWord_1561649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561649).length < 2 ^ (prefixWord ++ tailWord_1561649).sum := by decide
  have hdescent : baseEnd_1561649 < baseStart_1561649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561675 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_1561675 : Nat := 118140960795 + 1561675 * 2 ^ 59
def prefixEnd_1561675 : Nat := 4983230072969 + 3 ^ 40 * 1561675 * 2
def baseEnd_1561675 : Nat := 801889901110282673080493

theorem tailTrace_1561675 : CollatzResearch.WordTrace tailWord_1561675 prefixEnd_1561675 801889901110282673080493 := by
  unfold tailWord_1561675
  simp only [CollatzResearch.WordTrace]
  refine ⟨56958966617325662701014479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37972644411550441800676319 56958966617325662701014479)
  ·
    refine ⟨85438449925988494051521719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56958966617325662701014479 85438449925988494051521719)
    ·
      refine ⟨128157674888982741077282579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85438449925988494051521719 128157674888982741077282579)
      ·
        refine ⟨192236512333474111615923869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128157674888982741077282579 192236512333474111615923869)
        ·
          refine ⟨72088692125052791855971451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192236512333474111615923869 72088692125052791855971451)
          ·
            refine ⟨108133038187579187783957177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72088692125052791855971451 108133038187579187783957177)
            ·
              refine ⟨81099778640684390837967883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108133038187579187783957177 81099778640684390837967883)
              ·
                refine ⟨121649667961026586256951825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81099778640684390837967883 121649667961026586256951825)
                ·
                  refine ⟨91237250970769939692713869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121649667961026586256951825 91237250970769939692713869)
                  ·
                    refine ⟨34213969114038727384767701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91237250970769939692713869 34213969114038727384767701)
                    ·
                      refine ⟨801889901110282673080493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34213969114038727384767701 801889901110282673080493)
                      ·
                        rfl

theorem cell23_1561675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_1561675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561675 prefixEnd_1561675 := by exact prefixLift 1561675
  have htrace : WordTrace (prefixWord ++ tailWord_1561675) baseStart_1561675 baseEnd_1561675 := by
    simpa [prefixWord, tailWord_1561675, baseEnd_1561675] using wordTrace_append hprefix tailTrace_1561675
  have hstable : (prefixWord ++ tailWord_1561675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561675).length < 2 ^ (prefixWord ++ tailWord_1561675).sum := by decide
  have hdescent : baseEnd_1561675 < baseStart_1561675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561689 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 3, 3, 2]
def baseStart_1561689 : Nat := 118140960795 + 1561689 * 2 ^ 59
def prefixEnd_1561689 : Nat := 4983230072969 + 3 ^ 40 * 1561689 * 2
def baseEnd_1561689 : Nat := 801897089839445618305429

theorem tailTrace_1561689 : CollatzResearch.WordTrace tailWord_1561689 prefixEnd_1561689 801897089839445618305429 := by
  unfold tailWord_1561689
  simp only [CollatzResearch.WordTrace]
  refine ⟨56959477239274943092024121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37972984826183295394682747 56959477239274943092024121)
  ·
    refine ⟨42719607929456207319018091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56959477239274943092024121 42719607929456207319018091)
    ·
      refine ⟨64079411894184310978527137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42719607929456207319018091 64079411894184310978527137)
      ·
        refine ⟨48059558920638233233895353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64079411894184310978527137 48059558920638233233895353)
        ·
          refine ⟨36044669190478674925421515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48059558920638233233895353 36044669190478674925421515)
          ·
            refine ⟨54067003785718012388132273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36044669190478674925421515 54067003785718012388132273)
            ·
              refine ⟨40550252839288509291099205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54067003785718012388132273 40550252839288509291099205)
              ·
                refine ⟨7603172407366595492081101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40550252839288509291099205 7603172407366595492081101)
                ·
                  refine ⟨2851189652762473309530413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7603172407366595492081101 2851189652762473309530413)
                  ·
                    refine ⟨1069196119785927491073905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851189652762473309530413 1069196119785927491073905)
                    ·
                      refine ⟨801897089839445618305429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069196119785927491073905 801897089839445618305429)
                      ·
                        rfl

theorem cell23_1561689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_1561689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561689 prefixEnd_1561689 := by exact prefixLift 1561689
  have htrace : WordTrace (prefixWord ++ tailWord_1561689) baseStart_1561689 baseEnd_1561689 := by
    simpa [prefixWord, tailWord_1561689, baseEnd_1561689] using wordTrace_append hprefix tailTrace_1561689
  have hstable : (prefixWord ++ tailWord_1561689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561689).length < 2 ^ (prefixWord ++ tailWord_1561689).sum := by decide
  have hdescent : baseEnd_1561689 < baseStart_1561689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561693 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1561693 : Nat := 118140960795 + 1561693 * 2 ^ 59
def prefixEnd_1561693 : Nat := 4983230072969 + 3 ^ 40 * 1561693 * 2
def baseEnd_1561693 : Nat := 801899143762063602655411

theorem tailTrace_1561693 : CollatzResearch.WordTrace tailWord_1561693 prefixEnd_1561693 801899143762063602655411 := by
  unfold tailWord_1561693
  simp only [CollatzResearch.WordTrace]
  refine ⟨56959623131260451775169733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37973082087506967850113155 56959623131260451775169733)
  ·
    refine ⟨10679929337111334707844325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56959623131260451775169733 10679929337111334707844325)
    ·
      refine ⟨2002486750708375257720811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10679929337111334707844325 2002486750708375257720811)
      ·
        refine ⟨3003730126062562886581217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002486750708375257720811 3003730126062562886581217)
        ·
          refine ⟨2252797594546922164935913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3003730126062562886581217 2252797594546922164935913)
          ·
            refine ⟨1689598195910191623701935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2252797594546922164935913 1689598195910191623701935)
            ·
              refine ⟨2534397293865287435552903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689598195910191623701935 2534397293865287435552903)
              ·
                refine ⟨3801595940797931153329355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534397293865287435552903 3801595940797931153329355)
                ·
                  refine ⟨5702393911196896729994033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801595940797931153329355 5702393911196896729994033)
                  ·
                    refine ⟨4276795433397672547495525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5702393911196896729994033 4276795433397672547495525)
                    ·
                      refine ⟨801899143762063602655411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4276795433397672547495525 801899143762063602655411)
                      ·
                        rfl

theorem cell23_1561693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1561693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561693 prefixEnd_1561693 := by exact prefixLift 1561693
  have htrace : WordTrace (prefixWord ++ tailWord_1561693) baseStart_1561693 baseEnd_1561693 := by
    simpa [prefixWord, tailWord_1561693, baseEnd_1561693] using wordTrace_append hprefix tailTrace_1561693
  have hstable : (prefixWord ++ tailWord_1561693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561693).length < 2 ^ (prefixWord ++ tailWord_1561693).sum := by decide
  have hdescent : baseEnd_1561693 < baseStart_1561693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561719 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 3, 4, 2]
def baseStart_1561719 : Nat := 118140960795 + 1561719 * 2 ^ 59
def prefixEnd_1561719 : Nat := 4983230072969 + 3 ^ 40 * 1561719 * 2
def baseEnd_1561719 : Nat := 801912494259080500930291

theorem tailTrace_1561719 : CollatzResearch.WordTrace tailWord_1561719 prefixEnd_1561719 801912494259080500930291 := by
  unfold tailWord_1561719
  simp only [CollatzResearch.WordTrace]
  refine ⟨56960571429166258215616211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37973714286110838810410807 56960571429166258215616211)
  ·
    refine ⟨85440857143749387323424317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56960571429166258215616211 85440857143749387323424317)
    ·
      refine ⟨32040321428906020246284119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85440857143749387323424317 32040321428906020246284119)
      ·
        refine ⟨48060482143359030369426179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32040321428906020246284119 48060482143359030369426179)
        ·
          refine ⟨72090723215038545554139269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48060482143359030369426179 72090723215038545554139269)
          ·
            refine ⟨13517010602819727291401113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72090723215038545554139269 13517010602819727291401113)
            ·
              refine ⟨10137757952114795468550835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13517010602819727291401113 10137757952114795468550835)
              ·
                refine ⟨15206636928172193202826253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137757952114795468550835 15206636928172193202826253)
                ·
                  refine ⟨5702488848064572451059845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15206636928172193202826253 5702488848064572451059845)
                  ·
                    refine ⟨1069216659012107334573721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5702488848064572451059845 1069216659012107334573721)
                    ·
                      refine ⟨801912494259080500930291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069216659012107334573721 801912494259080500930291)
                      ·
                        rfl

theorem cell23_1561719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_1561719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561719 prefixEnd_1561719 := by exact prefixLift 1561719
  have htrace : WordTrace (prefixWord ++ tailWord_1561719) baseStart_1561719 baseEnd_1561719 := by
    simpa [prefixWord, tailWord_1561719, baseEnd_1561719] using wordTrace_append hprefix tailTrace_1561719
  have hstable : (prefixWord ++ tailWord_1561719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561719).length < 2 ^ (prefixWord ++ tailWord_1561719).sum := by decide
  have hdescent : baseEnd_1561719 < baseStart_1561719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561789 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1561789 : Nat := 118140960795 + 1561789 * 2 ^ 59
def prefixEnd_1561789 : Nat := 4983230072969 + 3 ^ 40 * 1561789 * 2
def baseEnd_1561789 : Nat := 267316145968298409018323

theorem tailTrace_1561789 : CollatzResearch.WordTrace tailWord_1561789 prefixEnd_1561789 267316145968298409018323 := by
  unfold tailWord_1561789
  simp only [CollatzResearch.WordTrace]
  refine ⟨56963124538912660170664421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37975416359275106780442947 56963124538912660170664421)
  ·
    refine ⟨10680585851046123781999579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56963124538912660170664421 10680585851046123781999579)
    ·
      refine ⟨16020878776569185672999369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10680585851046123781999579 16020878776569185672999369)
      ·
        refine ⟨12015659082426889254749527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16020878776569185672999369 12015659082426889254749527)
        ·
          refine ⟨18023488623640333882124291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015659082426889254749527 18023488623640333882124291)
          ·
            refine ⟨27035232935460500823186437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18023488623640333882124291 27035232935460500823186437)
            ·
              refine ⟨5069106175398843904347457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27035232935460500823186437 5069106175398843904347457)
              ·
                refine ⟨3801829631549132928260593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5069106175398843904347457 3801829631549132928260593)
                ·
                  refine ⟨2851372223661849696195445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801829631549132928260593 2851372223661849696195445)
                  ·
                    refine ⟨267316145968298409018323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2851372223661849696195445 267316145968298409018323)
                    ·
                      rfl

theorem cell23_1561789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1561789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561789 prefixEnd_1561789 := by exact prefixLift 1561789
  have htrace : WordTrace (prefixWord ++ tailWord_1561789) baseStart_1561789 baseEnd_1561789 := by
    simpa [prefixWord, tailWord_1561789, baseEnd_1561789] using wordTrace_append hprefix tailTrace_1561789
  have hstable : (prefixWord ++ tailWord_1561789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561789).length < 2 ^ (prefixWord ++ tailWord_1561789).sum := by decide
  have hdescent : baseEnd_1561789 < baseStart_1561789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561793 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 5]
def baseStart_1561793 : Nat := 118140960795 + 1561793 * 2 ^ 59
def prefixEnd_1561793 : Nat := 4983230072969 + 3 ^ 40 * 1561793 * 2
def baseEnd_1561793 : Nat := 89105610203057023489439

theorem tailTrace_1561793 : CollatzResearch.WordTrace tailWord_1561793 prefixEnd_1561793 89105610203057023489439 := by
  unfold tailWord_1561793
  simp only [CollatzResearch.WordTrace]
  refine ⟨56963270430898168853810033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37975513620598779235873355 56963270430898168853810033)
  ·
    refine ⟨42722452823173626640357525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56963270430898168853810033 42722452823173626640357525)
    ·
      refine ⟨2002614976086263748766759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42722452823173626640357525 2002614976086263748766759)
      ·
        refine ⟨3003922464129395623150139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002614976086263748766759 3003922464129395623150139)
        ·
          refine ⟨4505883696194093434725209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003922464129395623150139 4505883696194093434725209)
          ·
            refine ⟨3379412772145570076043907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505883696194093434725209 3379412772145570076043907)
            ·
              refine ⟨5069119158218355114065861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379412772145570076043907 5069119158218355114065861)
              ·
                refine ⟨950459842165941583887349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5069119158218355114065861 950459842165941583887349)
                ·
                  refine ⟨89105610203057023489439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 950459842165941583887349 89105610203057023489439)
                  ·
                    rfl

theorem cell23_1561793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 5].length) (baseStart_1561793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561793 prefixEnd_1561793 := by exact prefixLift 1561793
  have htrace : WordTrace (prefixWord ++ tailWord_1561793) baseStart_1561793 baseEnd_1561793 := by
    simpa [prefixWord, tailWord_1561793, baseEnd_1561793] using wordTrace_append hprefix tailTrace_1561793
  have hstable : (prefixWord ++ tailWord_1561793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561793).length < 2 ^ (prefixWord ++ tailWord_1561793).sum := by decide
  have hdescent : baseEnd_1561793 < baseStart_1561793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561846 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1561846 : Nat := 118140960795 + 1561846 * 2 ^ 59
def prefixEnd_1561846 : Nat := 4983230072969 + 3 ^ 40 * 1561846 * 2
def baseEnd_1561846 : Nat := 801977706302201504042207

theorem tailTrace_1561846 : CollatzResearch.WordTrace tailWord_1561846 prefixEnd_1561846 801977706302201504042207 := by
  unfold tailWord_1561846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560325218731634931593087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37976802333137439270326261 3560325218731634931593087)
  ·
    refine ⟨5340487828097452397389631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3560325218731634931593087 5340487828097452397389631)
    ·
      refine ⟨8010731742146178596084447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340487828097452397389631 8010731742146178596084447)
      ·
        refine ⟨12016097613219267894126671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010731742146178596084447 12016097613219267894126671)
        ·
          refine ⟨18024146419828901841190007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016097613219267894126671 18024146419828901841190007)
          ·
            refine ⟨27036219629743352761785011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18024146419828901841190007 27036219629743352761785011)
            ·
              refine ⟨40554329444615029142677517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27036219629743352761785011 40554329444615029142677517)
              ·
                refine ⟨15207873541730635928504069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40554329444615029142677517 15207873541730635928504069)
                ·
                  refine ⟨2851476289074494236594513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15207873541730635928504069 2851476289074494236594513)
                  ·
                    refine ⟨2138607216805870677445885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851476289074494236594513 2138607216805870677445885)
                    ·
                      refine ⟨801977706302201504042207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2138607216805870677445885 801977706302201504042207)
                      ·
                        rfl

theorem cell23_1561846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1561846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561846 prefixEnd_1561846 := by exact prefixLift 1561846
  have htrace : WordTrace (prefixWord ++ tailWord_1561846) baseStart_1561846 baseEnd_1561846 := by
    simpa [prefixWord, tailWord_1561846, baseEnd_1561846] using wordTrace_append hprefix tailTrace_1561846
  have hstable : (prefixWord ++ tailWord_1561846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561846).length < 2 ^ (prefixWord ++ tailWord_1561846).sum := by decide
  have hdescent : baseEnd_1561846 < baseStart_1561846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561887 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 1, 4]
def baseStart_1561887 : Nat := 118140960795 + 1561887 * 2 ^ 59
def prefixEnd_1561887 : Nat := 4983230072969 + 3 ^ 40 * 1561887 * 2
def baseEnd_1561887 : Nat := 267332919669678614543173

theorem tailTrace_1561887 : CollatzResearch.WordTrace tailWord_1561887 prefixEnd_1561887 267332919669678614543173 := by
  unfold tailWord_1561887
  simp only [CollatzResearch.WordTrace]
  refine ⟨56966698892557622907731915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37977799261705081938487943 56966698892557622907731915)
  ·
    refine ⟨85450048338836434361597873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56966698892557622907731915 85450048338836434361597873)
    ·
      refine ⟨64087536254127325771198405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85450048338836434361597873 64087536254127325771198405)
      ·
        refine ⟨12016413047648873582099701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64087536254127325771198405 12016413047648873582099701)
        ·
          refine ⟨1126538723217081898321847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12016413047648873582099701 1126538723217081898321847)
          ·
            refine ⟨1689808084825622847482771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126538723217081898321847 1689808084825622847482771)
            ·
              refine ⟨2534712127238434271224157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689808084825622847482771 2534712127238434271224157)
              ·
                refine ⟨950517047714412851709059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2534712127238434271224157 950517047714412851709059)
                ·
                  refine ⟨1425775571571619277563589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950517047714412851709059 1425775571571619277563589)
                  ·
                    refine ⟨267332919669678614543173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425775571571619277563589 267332919669678614543173)
                    ·
                      rfl

theorem cell23_1561887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 4].length) (baseStart_1561887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561887 prefixEnd_1561887 := by exact prefixLift 1561887
  have htrace : WordTrace (prefixWord ++ tailWord_1561887) baseStart_1561887 baseEnd_1561887 := by
    simpa [prefixWord, tailWord_1561887, baseEnd_1561887] using wordTrace_append hprefix tailTrace_1561887
  have hstable : (prefixWord ++ tailWord_1561887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561887).length < 2 ^ (prefixWord ++ tailWord_1561887).sum := by decide
  have hdescent : baseEnd_1561887 < baseStart_1561887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561917 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 6]
def baseStart_1561917 : Nat := 118140960795 + 1561917 * 2 ^ 59
def prefixEnd_1561917 : Nat := 4983230072969 + 3 ^ 40 * 1561917 * 2
def baseEnd_1561917 : Nat := 89112684825407858472709

theorem tailTrace_1561917 : CollatzResearch.WordTrace tailWord_1561917 prefixEnd_1561917 89112684825407858472709 := by
  unfold tailWord_1561917
  simp only [CollatzResearch.WordTrace]
  refine ⟨56967793082448938031324005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37978528721632625354216003 56967793082448938031324005)
  ·
    refine ⟨10681461202959175880873251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56967793082448938031324005 10681461202959175880873251)
    ·
      refine ⟨16022191804438763821309877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10681461202959175880873251 16022191804438763821309877)
      ·
        refine ⟨1502080481666134108247801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16022191804438763821309877 1502080481666134108247801)
        ·
          refine ⟨1126560361249600581185851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502080481666134108247801 1126560361249600581185851)
          ·
            refine ⟨1689840541874400871778777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126560361249600581185851 1689840541874400871778777)
            ·
              refine ⟨1267380406405800653834083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689840541874400871778777 1267380406405800653834083)
              ·
                refine ⟨1901070609608700980751125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267380406405800653834083 1901070609608700980751125)
                ·
                  refine ⟨89112684825407858472709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1901070609608700980751125 89112684825407858472709)
                  ·
                    rfl

theorem cell23_1561917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_1561917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561917 prefixEnd_1561917 := by exact prefixLift 1561917
  have htrace : WordTrace (prefixWord ++ tailWord_1561917) baseStart_1561917 baseEnd_1561917 := by
    simpa [prefixWord, tailWord_1561917, baseEnd_1561917] using wordTrace_append hprefix tailTrace_1561917
  have hstable : (prefixWord ++ tailWord_1561917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561917).length < 2 ^ (prefixWord ++ tailWord_1561917).sum := by decide
  have hdescent : baseEnd_1561917 < baseStart_1561917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561929 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_1561929 : Nat := 118140960795 + 1561929 * 2 ^ 59
def prefixEnd_1561929 : Nat := 4983230072969 + 3 ^ 40 * 1561929 * 2
def baseEnd_1561929 : Nat := 802020325196524679304325

theorem tailTrace_1561929 : CollatzResearch.WordTrace tailWord_1561929 prefixEnd_1561929 802020325196524679304325 := by
  unfold tailWord_1561929
  simp only [CollatzResearch.WordTrace]
  refine ⟨56968230758405464080760841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37978820505603642720507227 56968230758405464080760841)
  ·
    refine ⟨42726173068804098060570631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56968230758405464080760841 42726173068804098060570631)
    ·
      refine ⟨64089259603206147090855947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42726173068804098060570631 64089259603206147090855947)
      ·
        refine ⟨96133889404809220636283921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64089259603206147090855947 96133889404809220636283921)
        ·
          refine ⟨72100417053606915477212941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96133889404809220636283921 72100417053606915477212941)
          ·
            refine ⟨27037656395102593303954853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72100417053606915477212941 27037656395102593303954853)
            ·
              refine ⟨5069560574081736244491535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27037656395102593303954853 5069560574081736244491535)
              ·
                refine ⟨7604340861122604366737303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069560574081736244491535 7604340861122604366737303)
                ·
                  refine ⟨11406511291683906550105955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7604340861122604366737303 11406511291683906550105955)
                  ·
                    refine ⟨17109766937525859825158933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11406511291683906550105955 17109766937525859825158933)
                    ·
                      refine ⟨802020325196524679304325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17109766937525859825158933 802020325196524679304325)
                      ·
                        rfl

theorem cell23_1561929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_1561929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561929 prefixEnd_1561929 := by exact prefixLift 1561929
  have htrace : WordTrace (prefixWord ++ tailWord_1561929) baseStart_1561929 baseEnd_1561929 := by
    simpa [prefixWord, tailWord_1561929, baseEnd_1561929] using wordTrace_append hprefix tailTrace_1561929
  have hstable : (prefixWord ++ tailWord_1561929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561929).length < 2 ^ (prefixWord ++ tailWord_1561929).sum := by decide
  have hdescent : baseEnd_1561929 < baseStart_1561929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561936 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_1561936 : Nat := 118140960795 + 1561936 * 2 ^ 59
def prefixEnd_1561936 : Nat := 4983230072969 + 3 ^ 40 * 1561936 * 2
def baseEnd_1561936 : Nat := 802023919561106151916793

theorem tailTrace_1561936 : CollatzResearch.WordTrace tailWord_1561936 prefixEnd_1561936 802023919561106151916793 := by
  unfold tailWord_1561936
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484243034690052138132831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37978990712920069517510441 28484243034690052138132831)
  ·
    refine ⟨42726364552035078207199247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28484243034690052138132831 42726364552035078207199247)
    ·
      refine ⟨64089546828052617310798871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42726364552035078207199247 64089546828052617310798871)
      ·
        refine ⟨96134320242078925966198307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64089546828052617310798871 96134320242078925966198307)
        ·
          refine ⟨144201480363118388949297461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96134320242078925966198307 144201480363118388949297461)
          ·
            refine ⟨13518888784042348963996637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144201480363118388949297461 13518888784042348963996637)
            ·
              refine ⟨5069583294015880861498739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13518888784042348963996637 5069583294015880861498739)
              ·
                refine ⟨7604374941023821292248109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069583294015880861498739 7604374941023821292248109)
                ·
                  refine ⟨2851640602883932984593041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7604374941023821292248109 2851640602883932984593041)
                  ·
                    refine ⟨2138730452162949738444781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851640602883932984593041 2138730452162949738444781)
                    ·
                      refine ⟨802023919561106151916793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2138730452162949738444781 802023919561106151916793)
                      ·
                        rfl

theorem cell23_1561936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_1561936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561936 prefixEnd_1561936 := by exact prefixLift 1561936
  have htrace : WordTrace (prefixWord ++ tailWord_1561936) baseStart_1561936 baseEnd_1561936 := by
    simpa [prefixWord, tailWord_1561936, baseEnd_1561936] using wordTrace_append hprefix tailTrace_1561936
  have hstable : (prefixWord ++ tailWord_1561936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561936).length < 2 ^ (prefixWord ++ tailWord_1561936).sum := by decide
  have hdescent : baseEnd_1561936 < baseStart_1561936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561960 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1561960 : Nat := 118140960795 + 1561960 * 2 ^ 59
def prefixEnd_1561960 : Nat := 4983230072969 + 3 ^ 40 * 1561960 * 2
def baseEnd_1561960 : Nat := 267345414365604686005561

theorem tailTrace_1561960 : CollatzResearch.WordTrace tailWord_1561960 prefixEnd_1561960 267345414365604686005561 := by
  unfold tailWord_1561960
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484680710646578187569667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37979574280862104250092889 28484680710646578187569667)
  ·
    refine ⟨42727021065969867281354501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28484680710646578187569667 42727021065969867281354501)
    ·
      refine ⟨8011316449869350115253969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42727021065969867281354501 8011316449869350115253969)
      ·
        refine ⟨6008487337402012586440477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8011316449869350115253969 6008487337402012586440477)
        ·
          refine ⟨2253182751525754719915179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6008487337402012586440477 2253182751525754719915179)
          ·
            refine ⟨3379774127288632079872769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253182751525754719915179 3379774127288632079872769)
            ·
              refine ⟨2534830595466474059904577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3379774127288632079872769 2534830595466474059904577)
              ·
                refine ⟨1901122946599855544928433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534830595466474059904577 1901122946599855544928433)
                ·
                  refine ⟨1425842209949891658696325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901122946599855544928433 1425842209949891658696325)
                  ·
                    refine ⟨267345414365604686005561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1425842209949891658696325 267345414365604686005561)
                    ·
                      rfl

theorem cell23_1561960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1561960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561960 prefixEnd_1561960 := by exact prefixLift 1561960
  have htrace : WordTrace (prefixWord ++ tailWord_1561960) baseStart_1561960 baseEnd_1561960 := by
    simpa [prefixWord, tailWord_1561960, baseEnd_1561960] using wordTrace_append hprefix tailTrace_1561960
  have hstable : (prefixWord ++ tailWord_1561960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561960).length < 2 ^ (prefixWord ++ tailWord_1561960).sum := by decide
  have hdescent : baseEnd_1561960 < baseStart_1561960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561969 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_1561969 : Nat := 118140960795 + 1561969 * 2 ^ 59
def prefixEnd_1561969 : Nat := 4983230072969 + 3 ^ 40 * 1561969 * 2
def baseEnd_1561969 : Nat := 267346954807568174268047

theorem tailTrace_1561969 : CollatzResearch.WordTrace tailWord_1561969 prefixEnd_1561969 267346954807568174268047 := by
  unfold tailWord_1561969
  simp only [CollatzResearch.WordTrace]
  refine ⟨56969689678260550912216961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37979793118840367274811307 56969689678260550912216961)
  ·
    refine ⟨42727267258695413184162721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56969689678260550912216961 42727267258695413184162721)
    ·
      refine ⟨32045450444021559888122041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42727267258695413184162721 32045450444021559888122041)
      ·
        refine ⟨24034087833016169916091531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32045450444021559888122041 24034087833016169916091531)
        ·
          refine ⟨36051131749524254874137297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24034087833016169916091531 36051131749524254874137297)
          ·
            refine ⟨27038348812143191155602973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36051131749524254874137297 27038348812143191155602973)
            ·
              refine ⟨10139380804553696683351115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27038348812143191155602973 10139380804553696683351115)
              ·
                refine ⟨15209071206830545025026673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139380804553696683351115 15209071206830545025026673)
                ·
                  refine ⟨11406803405122908768770005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15209071206830545025026673 11406803405122908768770005)
                  ·
                    refine ⟨267346954807568174268047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11406803405122908768770005 267346954807568174268047)
                    ·
                      rfl

theorem cell23_1561969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_1561969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561969 prefixEnd_1561969 := by exact prefixLift 1561969
  have htrace : WordTrace (prefixWord ++ tailWord_1561969) baseStart_1561969 baseEnd_1561969 := by
    simpa [prefixWord, tailWord_1561969, baseEnd_1561969] using wordTrace_append hprefix tailTrace_1561969
  have hstable : (prefixWord ++ tailWord_1561969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561969).length < 2 ^ (prefixWord ++ tailWord_1561969).sum := by decide
  have hdescent : baseEnd_1561969 < baseStart_1561969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561973 : List Nat := [1, 3, 4, 1, 3, 2, 1, 8]
def baseStart_1561973 : Nat := 118140960795 + 1561973 * 2 ^ 59
def prefixEnd_1561973 : Nat := 4983230072969 + 3 ^ 40 * 1561973 * 2
def baseEnd_1561973 : Nat := 29705293272048981746449

theorem tailTrace_1561973 : CollatzResearch.WordTrace tailWord_1561973 prefixEnd_1561973 29705293272048981746449 := by
  unfold tailWord_1561973
  simp only [CollatzResearch.WordTrace]
  refine ⟨56969835570246059595362573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37979890380164039730241715 56969835570246059595362573)
  ·
    refine ⟨21363688338842272348260965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56969835570246059595362573 21363688338842272348260965)
    ·
      refine ⟨4005691563532926065298931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21363688338842272348260965 4005691563532926065298931)
      ·
        refine ⟨6008537345299389097948397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005691563532926065298931 6008537345299389097948397)
        ·
          refine ⟨2253201504487270911730649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6008537345299389097948397 2253201504487270911730649)
          ·
            refine ⟨1689901128365453183797987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253201504487270911730649 1689901128365453183797987)
            ·
              refine ⟨2534851692548179775696981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689901128365453183797987 2534851692548179775696981)
              ·
                refine ⟨29705293272048981746449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2534851692548179775696981 29705293272048981746449)
                ·
                  rfl

theorem cell23_1561973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 8].length) (baseStart_1561973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1561973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1561973 prefixEnd_1561973 := by exact prefixLift 1561973
  have htrace : WordTrace (prefixWord ++ tailWord_1561973) baseStart_1561973 baseEnd_1561973 := by
    simpa [prefixWord, tailWord_1561973, baseEnd_1561973] using wordTrace_append hprefix tailTrace_1561973
  have hstable : (prefixWord ++ tailWord_1561973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561973).length < 2 ^ (prefixWord ++ tailWord_1561973).sum := by decide
  have hdescent : baseEnd_1561973 < baseStart_1561973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562010 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1562010 : Nat := 118140960795 + 1562010 * 2 ^ 59
def prefixEnd_1562010 : Nat := 4983230072969 + 3 ^ 40 * 1562010 * 2
def baseEnd_1562010 : Nat := 802061917129538862391453

theorem tailTrace_1562010 : CollatzResearch.WordTrace tailWord_1562010 prefixEnd_1562010 802061917129538862391453 := by
  unfold tailWord_1562010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14242796267778003728614871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37980790047408009942972989 14242796267778003728614871)
  ·
    refine ⟨21364194401667005592922307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14242796267778003728614871 21364194401667005592922307)
    ·
      refine ⟨32046291602500508389383461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21364194401667005592922307 32046291602500508389383461)
      ·
        refine ⟨6008679675468845323009399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32046291602500508389383461 6008679675468845323009399)
        ·
          refine ⟨9013019513203267984514099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008679675468845323009399 9013019513203267984514099)
          ·
            refine ⟨13519529269804901976771149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9013019513203267984514099 13519529269804901976771149)
            ·
              refine ⟨5069823476176838241289181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13519529269804901976771149 5069823476176838241289181)
              ·
                refine ⟨1901183803566314340483443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069823476176838241289181 1901183803566314340483443)
                ·
                  refine ⟨2851775705349471510725165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901183803566314340483443 2851775705349471510725165)
                  ·
                    refine ⟨1069415889506051816521937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851775705349471510725165 1069415889506051816521937)
                    ·
                      refine ⟨802061917129538862391453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069415889506051816521937 802061917129538862391453)
                      ·
                        rfl

theorem cell23_1562010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1562010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562010 prefixEnd_1562010 := by exact prefixLift 1562010
  have htrace : WordTrace (prefixWord ++ tailWord_1562010) baseStart_1562010 baseEnd_1562010 := by
    simpa [prefixWord, tailWord_1562010, baseEnd_1562010] using wordTrace_append hprefix tailTrace_1562010
  have hstable : (prefixWord ++ tailWord_1562010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562010).length < 2 ^ (prefixWord ++ tailWord_1562010).sum := by decide
  have hdescent : baseEnd_1562010 < baseStart_1562010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562040 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 2, 2, 2]
def baseStart_1562040 : Nat := 118140960795 + 1562040 * 2 ^ 59
def prefixEnd_1562040 : Nat := 4983230072969 + 3 ^ 40 * 1562040 * 2
def baseEnd_1562040 : Nat := 802077321549173745016315

theorem tailTrace_1562040 : CollatzResearch.WordTrace tailWord_1562040 prefixEnd_1562040 802077321549173745016315 := by
  unfold tailWord_1562040
  simp only [CollatzResearch.WordTrace]
  refine ⟨28486139630501665019025787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37981519507335553358701049 28486139630501665019025787)
  ·
    refine ⟨42729209445752497528538681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28486139630501665019025787 42729209445752497528538681)
    ·
      refine ⟨32046907084314373146404011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42729209445752497528538681 32046907084314373146404011)
      ·
        refine ⟨48070360626471559719606017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32046907084314373146404011 48070360626471559719606017)
        ·
          refine ⟨36052770469853669789704513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48070360626471559719606017 36052770469853669789704513)
          ·
            refine ⟨27039577852390252342278385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36052770469853669789704513 27039577852390252342278385)
            ·
              refine ⟨20279683389292689256708789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27039577852390252342278385 20279683389292689256708789)
              ·
                refine ⟨1901220317746189617816449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20279683389292689256708789 1901220317746189617816449)
                ·
                  refine ⟨1425915238309642213362337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901220317746189617816449 1425915238309642213362337)
                  ·
                    refine ⟨1069436428732231660021753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425915238309642213362337 1069436428732231660021753)
                    ·
                      refine ⟨802077321549173745016315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069436428732231660021753 802077321549173745016315)
                      ·
                        rfl

theorem cell23_1562040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_1562040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562040 prefixEnd_1562040 := by exact prefixLift 1562040
  have htrace : WordTrace (prefixWord ++ tailWord_1562040) baseStart_1562040 baseEnd_1562040 := by
    simpa [prefixWord, tailWord_1562040, baseEnd_1562040] using wordTrace_append hprefix tailTrace_1562040
  have hstable : (prefixWord ++ tailWord_1562040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562040).length < 2 ^ (prefixWord ++ tailWord_1562040).sum := by decide
  have hdescent : baseEnd_1562040 < baseStart_1562040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562063 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 5]
def baseStart_1562063 : Nat := 118140960795 + 1562063 * 2 ^ 59
def prefixEnd_1562063 : Nat := 4983230072969 + 3 ^ 40 * 1562063 * 2
def baseEnd_1562063 : Nat := 89121014622691906114301

theorem tailTrace_1562063 : CollatzResearch.WordTrace tailWord_1562063 prefixEnd_1562063 89121014622691906114301 := by
  unfold tailWord_1562063
  simp only [CollatzResearch.WordTrace]
  refine ⟨56973118139920004966138843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37982078759946669977425895 56973118139920004966138843)
  ·
    refine ⟨85459677209880007449208265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56973118139920004966138843 85459677209880007449208265)
    ·
      refine ⟨64094757907410005586906199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85459677209880007449208265 64094757907410005586906199)
      ·
        refine ⟨96142136861115008380359299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64094757907410005586906199 96142136861115008380359299)
        ·
          refine ⟨144213205291672512570538949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96142136861115008380359299 144213205291672512570538949)
          ·
            refine ⟨27039975992188596106976053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144213205291672512570538949 27039975992188596106976053)
            ·
              refine ⟨2534997749267680885029005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27039975992188596106976053 2534997749267680885029005)
              ·
                refine ⟨950624155975380331885877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2534997749267680885029005 950624155975380331885877)
                ·
                  refine ⟨89121014622691906114301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 950624155975380331885877 89121014622691906114301)
                  ·
                    rfl

theorem cell23_1562063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 5].length) (baseStart_1562063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562063 prefixEnd_1562063 := by exact prefixLift 1562063
  have htrace : WordTrace (prefixWord ++ tailWord_1562063) baseStart_1562063 baseEnd_1562063 := by
    simpa [prefixWord, tailWord_1562063, baseEnd_1562063] using wordTrace_append hprefix tailTrace_1562063
  have hstable : (prefixWord ++ tailWord_1562063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562063).length < 2 ^ (prefixWord ++ tailWord_1562063).sum := by decide
  have hdescent : baseEnd_1562063 < baseStart_1562063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562176 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1562176 : Nat := 118140960795 + 1562176 * 2 ^ 59
def prefixEnd_1562176 : Nat := 4983230072969 + 3 ^ 40 * 1562176 * 2
def baseEnd_1562176 : Nat := 802147154918185212915689

theorem tailTrace_1562176 : CollatzResearch.WordTrace tailWord_1562176 prefixEnd_1562176 802147154918185212915689 := by
  unfold tailWord_1562176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28488619794255312632501191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37984826392340416843334921 28488619794255312632501191)
  ·
    refine ⟨42732929691382968948751787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28488619794255312632501191 42732929691382968948751787)
    ·
      refine ⟨64099394537074453423127681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42732929691382968948751787 64099394537074453423127681)
      ·
        refine ⟨48074545902805840067345761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64099394537074453423127681 48074545902805840067345761)
        ·
          refine ⟨36055909427104380050509321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48074545902805840067345761 36055909427104380050509321)
          ·
            refine ⟨27041932070328285037881991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36055909427104380050509321 27041932070328285037881991)
            ·
              refine ⟨40562898105492427556822987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27041932070328285037881991 40562898105492427556822987)
              ·
                refine ⟨60844347158238641335234481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40562898105492427556822987 60844347158238641335234481)
                ·
                  refine ⟨45633260368678981001425861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60844347158238641335234481 45633260368678981001425861)
                  ·
                    refine ⟨8556236319127308937767349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45633260368678981001425861 8556236319127308937767349)
                    ·
                      refine ⟨802147154918185212915689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8556236319127308937767349 802147154918185212915689)
                      ·
                        rfl

theorem cell23_1562176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1562176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562176 prefixEnd_1562176 := by exact prefixLift 1562176
  have htrace : WordTrace (prefixWord ++ tailWord_1562176) baseStart_1562176 baseEnd_1562176 := by
    simpa [prefixWord, tailWord_1562176, baseEnd_1562176] using wordTrace_append hprefix tailTrace_1562176
  have hstable : (prefixWord ++ tailWord_1562176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562176).length < 2 ^ (prefixWord ++ tailWord_1562176).sum := by decide
  have hdescent : baseEnd_1562176 < baseStart_1562176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562190 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_1562190 : Nat := 118140960795 + 1562190 * 2 ^ 59
def prefixEnd_1562190 : Nat := 4983230072969 + 3 ^ 40 * 1562190 * 2
def baseEnd_1562190 : Nat := 802154343647348158140625

theorem tailTrace_1562190 : CollatzResearch.WordTrace tailWord_1562190 prefixEnd_1562190 802154343647348158140625 := by
  unfold tailWord_1562190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122218776307488207001503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37985166806973270437341349 7122218776307488207001503)
  ·
    refine ⟨10683328164461232310502255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7122218776307488207001503 10683328164461232310502255)
    ·
      refine ⟨16024992246691848465753383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683328164461232310502255 16024992246691848465753383)
      ·
        refine ⟨24037488370037772698630075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16024992246691848465753383 24037488370037772698630075)
        ·
          refine ⟨36056232555056659047945113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24037488370037772698630075 36056232555056659047945113)
          ·
            refine ⟨27042174416292494285958835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36056232555056659047945113 27042174416292494285958835)
            ·
              refine ⟨40563261624438741428938253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27042174416292494285958835 40563261624438741428938253)
              ·
                refine ⟨15211223109164528035851845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40563261624438741428938253 15211223109164528035851845)
                ·
                  refine ⟨2852104332968349006722221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15211223109164528035851845 2852104332968349006722221)
                  ·
                    refine ⟨1069539124863130877520833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852104332968349006722221 1069539124863130877520833)
                    ·
                      refine ⟨802154343647348158140625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069539124863130877520833 802154343647348158140625)
                      ·
                        rfl

theorem cell23_1562190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_1562190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562190 prefixEnd_1562190 := by exact prefixLift 1562190
  have htrace : WordTrace (prefixWord ++ tailWord_1562190) baseStart_1562190 baseEnd_1562190 := by
    simpa [prefixWord, tailWord_1562190, baseEnd_1562190] using wordTrace_append hprefix tailTrace_1562190
  have hstable : (prefixWord ++ tailWord_1562190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562190).length < 2 ^ (prefixWord ++ tailWord_1562190).sum := by decide
  have hdescent : baseEnd_1562190 < baseStart_1562190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562233 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1562233 : Nat := 118140960795 + 1562233 * 2 ^ 59
def prefixEnd_1562233 : Nat := 4983230072969 + 3 ^ 40 * 1562233 * 2
def baseEnd_1562233 : Nat := 802176423315491489902927

theorem tailTrace_1562233 : CollatzResearch.WordTrace tailWord_1562233 prefixEnd_1562233 802176423315491489902927 := by
  unfold tailWord_1562233
  simp only [CollatzResearch.WordTrace]
  refine ⟨56979318549304123999827353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37986212366202749333218235 56979318549304123999827353)
  ·
    refine ⟨42734488911978092999870515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56979318549304123999827353 42734488911978092999870515)
    ·
      refine ⟨64101733367967139499805773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42734488911978092999870515 64101733367967139499805773)
      ·
        refine ⟨24038150012987677312427165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64101733367967139499805773 24038150012987677312427165)
        ·
          refine ⟨9014306254870378992160187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24038150012987677312427165 9014306254870378992160187)
          ·
            refine ⟨13521459382305568488240281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9014306254870378992160187 13521459382305568488240281)
            ·
              refine ⟨10141094536729176366180211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13521459382305568488240281 10141094536729176366180211)
              ·
                refine ⟨15211641805093764549270317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10141094536729176366180211 15211641805093764549270317)
                ·
                  refine ⟨5704365676910161705976369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15211641805093764549270317 5704365676910161705976369)
                  ·
                    refine ⟨4278274257682621279482277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5704365676910161705976369 4278274257682621279482277)
                    ·
                      refine ⟨802176423315491489902927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4278274257682621279482277 802176423315491489902927)
                      ·
                        rfl

theorem cell23_1562233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1562233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562233 prefixEnd_1562233 := by exact prefixLift 1562233
  have htrace : WordTrace (prefixWord ++ tailWord_1562233) baseStart_1562233 baseEnd_1562233 := by
    simpa [prefixWord, tailWord_1562233, baseEnd_1562233] using wordTrace_append hprefix tailTrace_1562233
  have hstable : (prefixWord ++ tailWord_1562233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562233).length < 2 ^ (prefixWord ++ tailWord_1562233).sum := by decide
  have hdescent : baseEnd_1562233 < baseStart_1562233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562240 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3]
def baseStart_1562240 : Nat := 118140960795 + 1562240 * 2 ^ 59
def prefixEnd_1562240 : Nat := 4983230072969 + 3 ^ 40 * 1562240 * 2
def baseEnd_1562240 : Nat := 802180017680072962515395

theorem tailTrace_1562240 : CollatzResearch.WordTrace tailWord_1562240 prefixEnd_1562240 802180017680072962515395 := by
  unfold tailWord_1562240
  simp only [CollatzResearch.WordTrace]
  refine ⟨28489786930139382097666087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37986382573519176130221449 28489786930139382097666087)
  ·
    refine ⟨42734680395209073146499131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28489786930139382097666087 42734680395209073146499131)
    ·
      refine ⟨64102020592813609719748697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42734680395209073146499131 64102020592813609719748697)
      ·
        refine ⟨48076515444610207289811523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64102020592813609719748697 48076515444610207289811523)
        ·
          refine ⟨72114773166915310934717285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48076515444610207289811523 72114773166915310934717285)
          ·
            refine ⟨13521519968796620800259491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72114773166915310934717285 13521519968796620800259491)
            ·
              refine ⟨20282279953194931200389237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13521519968796620800259491 20282279953194931200389237)
              ·
                refine ⟨1901463745612024800036491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20282279953194931200389237 1901463745612024800036491)
                ·
                  refine ⟨2852195618418037200054737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901463745612024800036491 2852195618418037200054737)
                  ·
                    refine ⟨2139146713813527900041053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852195618418037200054737 2139146713813527900041053)
                    ·
                      refine ⟨802180017680072962515395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2139146713813527900041053 802180017680072962515395)
                      ·
                        rfl

theorem cell23_1562240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_1562240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562240 prefixEnd_1562240 := by exact prefixLift 1562240
  have htrace : WordTrace (prefixWord ++ tailWord_1562240) baseStart_1562240 baseEnd_1562240 := by
    simpa [prefixWord, tailWord_1562240, baseEnd_1562240] using wordTrace_append hprefix tailTrace_1562240
  have hstable : (prefixWord ++ tailWord_1562240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562240).length < 2 ^ (prefixWord ++ tailWord_1562240).sum := by decide
  have hdescent : baseEnd_1562240 < baseStart_1562240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562248 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1562248 : Nat := 118140960795 + 1562248 * 2 ^ 59
def prefixEnd_1562248 : Nat := 4983230072969 + 3 ^ 40 * 1562248 * 2
def baseEnd_1562248 : Nat := 802184125525308931215359

theorem tailTrace_1562248 : CollatzResearch.WordTrace tailWord_1562248 prefixEnd_1562248 802184125525308931215359 := by
  unfold tailWord_1562248
  simp only [CollatzResearch.WordTrace]
  refine ⟨28489932822124890780811699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37986577096166521041082265 28489932822124890780811699)
  ·
    refine ⟨42734899233187336171217549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28489932822124890780811699 42734899233187336171217549)
    ·
      refine ⟨16025587212445251064206581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42734899233187336171217549 16025587212445251064206581)
      ·
        refine ⟨1502398801166742287269367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16025587212445251064206581 1502398801166742287269367)
        ·
          refine ⟨2253598201750113430904051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502398801166742287269367 2253598201750113430904051)
          ·
            refine ⟨3380397302625170146356077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253598201750113430904051 3380397302625170146356077)
            ·
              refine ⟨1267648988484438804883529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3380397302625170146356077 1267648988484438804883529)
              ·
                refine ⟨950736741363329103662647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267648988484438804883529 950736741363329103662647)
                ·
                  refine ⟨1426105112044993655493971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950736741363329103662647 1426105112044993655493971)
                  ·
                    refine ⟨2139157668067490483240957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1426105112044993655493971 2139157668067490483240957)
                    ·
                      refine ⟨802184125525308931215359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2139157668067490483240957 802184125525308931215359)
                      ·
                        rfl

theorem cell23_1562248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1562248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562248 prefixEnd_1562248 := by exact prefixLift 1562248
  have htrace : WordTrace (prefixWord ++ tailWord_1562248) baseStart_1562248 baseEnd_1562248 := by
    simpa [prefixWord, tailWord_1562248, baseEnd_1562248] using wordTrace_append hprefix tailTrace_1562248
  have hstable : (prefixWord ++ tailWord_1562248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562248).length < 2 ^ (prefixWord ++ tailWord_1562248).sum := by decide
  have hdescent : baseEnd_1562248 < baseStart_1562248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562254 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1562254 : Nat := 118140960795 + 1562254 * 2 ^ 59
def prefixEnd_1562254 : Nat := 4983230072969 + 3 ^ 40 * 1562254 * 2
def baseEnd_1562254 : Nat := 802187206409235907740331

theorem tailTrace_1562254 : CollatzResearch.WordTrace tailWord_1562254 prefixEnd_1562254 802187206409235907740331 := by
  unfold tailWord_1562254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122510560278505573292727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37986722988152029724227877 7122510560278505573292727)
  ·
    refine ⟨10683765840417758359939091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7122510560278505573292727 10683765840417758359939091)
    ·
      refine ⟨16025648760626637539908637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683765840417758359939091 16025648760626637539908637)
      ·
        refine ⟨6009618285234989077465739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16025648760626637539908637 6009618285234989077465739)
        ·
          refine ⟨9014427427852483616198609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009618285234989077465739 9014427427852483616198609)
          ·
            refine ⟨6760820570889362712148957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014427427852483616198609 6760820570889362712148957)
            ·
              refine ⟨2535307714083511017055859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760820570889362712148957 2535307714083511017055859)
              ·
                refine ⟨3802961571125266525583789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535307714083511017055859 3802961571125266525583789)
                ·
                  refine ⟨1426110589171974947093921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3802961571125266525583789 1426110589171974947093921)
                  ·
                    refine ⟨1069582941878981210320441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1426110589171974947093921 1069582941878981210320441)
                    ·
                      refine ⟨802187206409235907740331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069582941878981210320441 802187206409235907740331)
                      ·
                        rfl

theorem cell23_1562254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1562254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562254 prefixEnd_1562254 := by exact prefixLift 1562254
  have htrace : WordTrace (prefixWord ++ tailWord_1562254) baseStart_1562254 baseEnd_1562254 := by
    simpa [prefixWord, tailWord_1562254, baseEnd_1562254] using wordTrace_append hprefix tailTrace_1562254
  have hstable : (prefixWord ++ tailWord_1562254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562254).length < 2 ^ (prefixWord ++ tailWord_1562254).sum := by decide
  have hdescent : baseEnd_1562254 < baseStart_1562254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562264 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 2, 4]
def baseStart_1562264 : Nat := 118140960795 + 1562264 * 2 ^ 59
def prefixEnd_1562264 : Nat := 4983230072969 + 3 ^ 40 * 1562264 * 2
def baseEnd_1562264 : Nat := 267397447071926956205095

theorem tailTrace_1562264 : CollatzResearch.WordTrace tailWord_1562264 prefixEnd_1562264 267397447071926956205095 := by
  unfold tailWord_1562264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490224606095908147102923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37986966141461210862803897 28490224606095908147102923)
  ·
    refine ⟨42735336909143862220654385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28490224606095908147102923 42735336909143862220654385)
    ·
      refine ⟨32051502681857896665490789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42735336909143862220654385 32051502681857896665490789)
      ·
        refine ⟨6009656752848355624779523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32051502681857896665490789 6009656752848355624779523)
        ·
          refine ⟨9014485129272533437169285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009656752848355624779523 9014485129272533437169285)
          ·
            refine ⟨1690215961738600019469241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9014485129272533437169285 1690215961738600019469241)
            ·
              refine ⟨1267661971303950014601931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690215961738600019469241 1267661971303950014601931)
              ·
                refine ⟨1901492956955925021902897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267661971303950014601931 1901492956955925021902897)
                ·
                  refine ⟨1426119717716943766427173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901492956955925021902897 1426119717716943766427173)
                  ·
                    refine ⟨267397447071926956205095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426119717716943766427173 267397447071926956205095)
                    ·
                      rfl

theorem cell23_1562264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_1562264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562264 prefixEnd_1562264 := by exact prefixLift 1562264
  have htrace : WordTrace (prefixWord ++ tailWord_1562264) baseStart_1562264 baseEnd_1562264 := by
    simpa [prefixWord, tailWord_1562264, baseEnd_1562264] using wordTrace_append hprefix tailTrace_1562264
  have hstable : (prefixWord ++ tailWord_1562264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562264).length < 2 ^ (prefixWord ++ tailWord_1562264).sum := by decide
  have hdescent : baseEnd_1562264 < baseStart_1562264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562271 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1562271 : Nat := 118140960795 + 1562271 * 2 ^ 59
def prefixEnd_1562271 : Nat := 4983230072969 + 3 ^ 40 * 1562271 * 2
def baseEnd_1562271 : Nat := 802195935580362341227753

theorem tailTrace_1562271 : CollatzResearch.WordTrace tailWord_1562271 prefixEnd_1562271 802195935580362341227753 := by
  unfold tailWord_1562271
  simp only [CollatzResearch.WordTrace]
  refine ⟨56980704523166456489710667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37987136348777637659807111 56980704523166456489710667)
  ·
    refine ⟨85471056784749684734566001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56980704523166456489710667 85471056784749684734566001)
    ·
      refine ⟨64103292588562263550924501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85471056784749684734566001 64103292588562263550924501)
      ·
        refine ⟨1502420920044428051974793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 64103292588562263550924501 1502420920044428051974793)
        ·
          refine ⟨1126815690033321038981095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502420920044428051974793 1126815690033321038981095)
          ·
            refine ⟨1690223535049981558471643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126815690033321038981095 1690223535049981558471643)
            ·
              refine ⟨2535335302574972337707465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690223535049981558471643 2535335302574972337707465)
              ·
                refine ⟨1901501476931229253280599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535335302574972337707465 1901501476931229253280599)
                ·
                  refine ⟨2852252215396843879920899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901501476931229253280599 2852252215396843879920899)
                  ·
                    refine ⟨4278378323095265819881349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852252215396843879920899 4278378323095265819881349)
                    ·
                      refine ⟨802195935580362341227753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4278378323095265819881349 802195935580362341227753)
                      ·
                        rfl

theorem cell23_1562271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1562271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562271 prefixEnd_1562271 := by exact prefixLift 1562271
  have htrace : WordTrace (prefixWord ++ tailWord_1562271) baseStart_1562271 baseEnd_1562271 := by
    simpa [prefixWord, tailWord_1562271, baseEnd_1562271] using wordTrace_append hprefix tailTrace_1562271
  have hstable : (prefixWord ++ tailWord_1562271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562271).length < 2 ^ (prefixWord ++ tailWord_1562271).sum := by decide
  have hdescent : baseEnd_1562271 < baseStart_1562271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562274 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1562274 : Nat := 118140960795 + 1562274 * 2 ^ 59
def prefixEnd_1562274 : Nat := 4983230072969 + 3 ^ 40 * 1562274 * 2
def baseEnd_1562274 : Nat := 802197476022325829490239

theorem tailTrace_1562274 : CollatzResearch.WordTrace tailWord_1562274 prefixEnd_1562274 802197476022325829490239 := by
  unfold tailWord_1562274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245203485538897000517469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37987209294770392001379917 14245203485538897000517469)
  ·
    refine ⟨5341951307077086375194051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14245203485538897000517469 5341951307077086375194051)
    ·
      refine ⟨8012926960615629562791077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5341951307077086375194051 8012926960615629562791077)
      ·
        refine ⟨1502423805115430543023327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8012926960615629562791077 1502423805115430543023327)
        ·
          refine ⟨2253635707673145814534991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502423805115430543023327 2253635707673145814534991)
          ·
            refine ⟨3380453561509718721802487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253635707673145814534991 3380453561509718721802487)
            ·
              refine ⟨5070680342264578082703731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380453561509718721802487 5070680342264578082703731)
              ·
                refine ⟨7606020513396867124055597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070680342264578082703731 7606020513396867124055597)
                ·
                  refine ⟨2852257692523825171520849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7606020513396867124055597 2852257692523825171520849)
                  ·
                    refine ⟨2139193269392868878640637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852257692523825171520849 2139193269392868878640637)
                    ·
                      refine ⟨802197476022325829490239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2139193269392868878640637 802197476022325829490239)
                      ·
                        rfl

theorem cell23_1562274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1562274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562274 prefixEnd_1562274 := by exact prefixLift 1562274
  have htrace : WordTrace (prefixWord ++ tailWord_1562274) baseStart_1562274 baseEnd_1562274 := by
    simpa [prefixWord, tailWord_1562274, baseEnd_1562274] using wordTrace_append hprefix tailTrace_1562274
  have hstable : (prefixWord ++ tailWord_1562274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562274).length < 2 ^ (prefixWord ++ tailWord_1562274).sum := by decide
  have hdescent : baseEnd_1562274 < baseStart_1562274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562297 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1562297 : Nat := 118140960795 + 1562297 * 2 ^ 59
def prefixEnd_1562297 : Nat := 4983230072969 + 3 ^ 40 * 1562297 * 2
def baseEnd_1562297 : Nat := 802209286077379239502633

theorem tailTrace_1562297 : CollatzResearch.WordTrace tailWord_1562297 prefixEnd_1562297 802209286077379239502633 := by
  unfold tailWord_1562297
  simp only [CollatzResearch.WordTrace]
  refine ⟨56981652821072262930157145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37987768547381508620104763 56981652821072262930157145)
  ·
    refine ⟨42736239615804197197617859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56981652821072262930157145 42736239615804197197617859)
    ·
      refine ⟨64104359423706295796426789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42736239615804197197617859 64104359423706295796426789)
      ·
        refine ⟨12019567391944930461830023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64104359423706295796426789 12019567391944930461830023)
        ·
          refine ⟨18029351087917395692745035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019567391944930461830023 18029351087917395692745035)
          ·
            refine ⟨27044026631876093539117553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18029351087917395692745035 27044026631876093539117553)
            ·
              refine ⟨20283019973907070154338165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27044026631876093539117553 20283019973907070154338165)
              ·
                refine ⟨1901533122553787826969203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20283019973907070154338165 1901533122553787826969203)
                ·
                  refine ⟨2852299683830681740453805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901533122553787826969203 2852299683830681740453805)
                  ·
                    refine ⟨1069612381436505652670177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852299683830681740453805 1069612381436505652670177)
                    ·
                      refine ⟨802209286077379239502633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069612381436505652670177 802209286077379239502633)
                      ·
                        rfl

theorem cell23_1562297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1562297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562297 prefixEnd_1562297 := by exact prefixLift 1562297
  have htrace : WordTrace (prefixWord ++ tailWord_1562297) baseStart_1562297 baseEnd_1562297 := by
    simpa [prefixWord, tailWord_1562297, baseEnd_1562297] using wordTrace_append hprefix tailTrace_1562297
  have hstable : (prefixWord ++ tailWord_1562297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562297).length < 2 ^ (prefixWord ++ tailWord_1562297).sum := by decide
  have hdescent : baseEnd_1562297 < baseStart_1562297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562303 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 2, 6]
def baseStart_1562303 : Nat := 118140960795 + 1562303 * 2 ^ 59
def prefixEnd_1562303 : Nat := 4983230072969 + 3 ^ 40 * 1562303 * 2
def baseEnd_1562303 : Nat := 267404122320435405342535

theorem tailTrace_1562303 : CollatzResearch.WordTrace tailWord_1562303 prefixEnd_1562303 267404122320435405342535 := by
  unfold tailWord_1562303
  simp only [CollatzResearch.WordTrace]
  refine ⟨56981871659050525954875563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37987914439367017303250375 56981871659050525954875563)
  ·
    refine ⟨85472807488575788932313345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56981871659050525954875563 85472807488575788932313345)
    ·
      refine ⟨64104605616431841699235009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85472807488575788932313345 64104605616431841699235009)
      ·
        refine ⟨48078454212323881274426257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64104605616431841699235009 48078454212323881274426257)
        ·
          refine ⟨36058840659242910955819693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48078454212323881274426257 36058840659242910955819693)
          ·
            refine ⟨13522065247216091608432385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36058840659242910955819693 13522065247216091608432385)
            ·
              refine ⟨10141548935412068706324289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13522065247216091608432385 10141548935412068706324289)
              ·
                refine ⟨7606161701559051529743217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10141548935412068706324289 7606161701559051529743217)
                ·
                  refine ⟨5704621276169288647307413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606161701559051529743217 5704621276169288647307413)
                  ·
                    refine ⟨267404122320435405342535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5704621276169288647307413 267404122320435405342535)
                    ·
                      rfl

theorem cell23_1562303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_1562303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562303 prefixEnd_1562303 := by exact prefixLift 1562303
  have htrace : WordTrace (prefixWord ++ tailWord_1562303) baseStart_1562303 baseEnd_1562303 := by
    simpa [prefixWord, tailWord_1562303, baseEnd_1562303] using wordTrace_append hprefix tailTrace_1562303
  have hstable : (prefixWord ++ tailWord_1562303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562303).length < 2 ^ (prefixWord ++ tailWord_1562303).sum := by decide
  have hdescent : baseEnd_1562303 < baseStart_1562303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562327 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 1, 4, 2]
def baseStart_1562327 : Nat := 118140960795 + 1562327 * 2 ^ 59
def prefixEnd_1562327 : Nat := 4983230072969 + 3 ^ 40 * 1562327 * 2
def baseEnd_1562327 : Nat := 802224690497014122127495

theorem tailTrace_1562327 : CollatzResearch.WordTrace tailWord_1562327 prefixEnd_1562327 802224690497014122127495 := by
  unfold tailWord_1562327
  simp only [CollatzResearch.WordTrace]
  refine ⟨56982747010963578053749235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37988498007309052035832823 56982747010963578053749235)
  ·
    refine ⟨85474120516445367080623853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56982747010963578053749235 85474120516445367080623853)
    ·
      refine ⟨32052795193667012655233945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85474120516445367080623853 32052795193667012655233945)
      ·
        refine ⟨24039596395250259491425459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32052795193667012655233945 24039596395250259491425459)
        ·
          refine ⟨36059394592875389237138189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24039596395250259491425459 36059394592875389237138189)
          ·
            refine ⟨13522272972328270963926821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36059394592875389237138189 13522272972328270963926821)
            ·
              refine ⟨2535426182311550805736279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13522272972328270963926821 2535426182311550805736279)
              ·
                refine ⟨3803139273467326208604419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535426182311550805736279 3803139273467326208604419)
                ·
                  refine ⟨5704708910200989312906629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803139273467326208604419 5704708910200989312906629)
                  ·
                    refine ⟨1069632920662685496169993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704708910200989312906629 1069632920662685496169993)
                    ·
                      refine ⟨802224690497014122127495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069632920662685496169993 802224690497014122127495)
                      ·
                        rfl

theorem cell23_1562327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_1562327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562327 prefixEnd_1562327 := by exact prefixLift 1562327
  have htrace : WordTrace (prefixWord ++ tailWord_1562327) baseStart_1562327 baseEnd_1562327 := by
    simpa [prefixWord, tailWord_1562327, baseEnd_1562327] using wordTrace_append hprefix tailTrace_1562327
  have hstable : (prefixWord ++ tailWord_1562327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562327).length < 2 ^ (prefixWord ++ tailWord_1562327).sum := by decide
  have hdescent : baseEnd_1562327 < baseStart_1562327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562400 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1562400 : Nat := 118140960795 + 1562400 * 2 ^ 59
def prefixEnd_1562400 : Nat := 4983230072969 + 3 ^ 40 * 1562400 * 2
def baseEnd_1562400 : Nat := 802262174584792336514659

theorem tailTrace_1562400 : CollatzResearch.WordTrace tailWord_1562400 prefixEnd_1562400 802262174584792336514659 := by
  unfold tailWord_1562400
  simp only [CollatzResearch.WordTrace]
  refine ⟨28492704769849555760578327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37990273026466074347437769 28492704769849555760578327)
  ·
    refine ⟨42739057154774333640867491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28492704769849555760578327 42739057154774333640867491)
    ·
      refine ⟨64108585732161500461301237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42739057154774333640867491 64108585732161500461301237)
      ·
        refine ⟨6010179912390140668246991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64108585732161500461301237 6010179912390140668246991)
        ·
          refine ⟨9015269868585211002370487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010179912390140668246991 9015269868585211002370487)
          ·
            refine ⟨13522904802877816503555731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015269868585211002370487 13522904802877816503555731)
            ·
              refine ⟨20284357204316724755333597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13522904802877816503555731 20284357204316724755333597)
              ·
                refine ⟨7606633951618771783250099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20284357204316724755333597 7606633951618771783250099)
                ·
                  refine ⟨11409950927428157674875149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7606633951618771783250099 11409950927428157674875149)
                  ·
                    refine ⟨4278731597785559128078181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11409950927428157674875149 4278731597785559128078181)
                    ·
                      refine ⟨802262174584792336514659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4278731597785559128078181 802262174584792336514659)
                      ·
                        rfl

theorem cell23_1562400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1562400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562400 prefixEnd_1562400 := by exact prefixLift 1562400
  have htrace : WordTrace (prefixWord ++ tailWord_1562400) baseStart_1562400 baseEnd_1562400 := by
    simpa [prefixWord, tailWord_1562400, baseEnd_1562400] using wordTrace_append hprefix tailTrace_1562400
  have hstable : (prefixWord ++ tailWord_1562400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562400).length < 2 ^ (prefixWord ++ tailWord_1562400).sum := by decide
  have hdescent : baseEnd_1562400 < baseStart_1562400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562414 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1562414 : Nat := 118140960795 + 1562414 * 2 ^ 59
def prefixEnd_1562414 : Nat := 4983230072969 + 3 ^ 40 * 1562414 * 2
def baseEnd_1562414 : Nat := 267423121104651760579865

theorem tailTrace_1562414 : CollatzResearch.WordTrace tailWord_1562414 prefixEnd_1562414 267423121104651760579865 := by
  unfold tailWord_1562414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123240020206048989020787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37990613441098927941444197 7123240020206048989020787)
  ·
    refine ⟨10684860030309073483531181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7123240020206048989020787 10684860030309073483531181)
    ·
      refine ⟨4006822511365902556324193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10684860030309073483531181 4006822511365902556324193)
      ·
        refine ⟨3005116883524426917243145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4006822511365902556324193 3005116883524426917243145)
        ·
          refine ⟨2253837662643320187932359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005116883524426917243145 2253837662643320187932359)
          ·
            refine ⟨3380756493964980281898539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253837662643320187932359 3380756493964980281898539)
            ·
              refine ⟨5071134740947470422847809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380756493964980281898539 5071134740947470422847809)
              ·
                refine ⟨3803351055710602817135857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5071134740947470422847809 3803351055710602817135857)
                ·
                  refine ⟨2852513291782952112851893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803351055710602817135857 2852513291782952112851893)
                  ·
                    refine ⟨267423121104651760579865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2852513291782952112851893 267423121104651760579865)
                    ·
                      rfl

theorem cell23_1562414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1562414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562414 prefixEnd_1562414 := by exact prefixLift 1562414
  have htrace : WordTrace (prefixWord ++ tailWord_1562414) baseStart_1562414 baseEnd_1562414 := by
    simpa [prefixWord, tailWord_1562414, baseEnd_1562414] using wordTrace_append hprefix tailTrace_1562414
  have hstable : (prefixWord ++ tailWord_1562414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562414).length < 2 ^ (prefixWord ++ tailWord_1562414).sum := by decide
  have hdescent : baseEnd_1562414 < baseStart_1562414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562417 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1562417 : Nat := 118140960795 + 1562417 * 2 ^ 59
def prefixEnd_1562417 : Nat := 4983230072969 + 3 ^ 40 * 1562417 * 2
def baseEnd_1562417 : Nat := 802270903755918770002081

theorem tailTrace_1562417 : CollatzResearch.WordTrace tailWord_1562417 prefixEnd_1562417 802270903755918770002081 := by
  unfold tailWord_1562417
  simp only [CollatzResearch.WordTrace]
  refine ⟨56986029580637523424525505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37990686387091682283017003 56986029580637523424525505)
  ·
    refine ⟨42739522185478142568394129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56986029580637523424525505 42739522185478142568394129)
    ·
      refine ⟨32054641639108606926295597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42739522185478142568394129 32054641639108606926295597)
      ·
        refine ⟨12020490614665727597360849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32054641639108606926295597 12020490614665727597360849)
        ·
          refine ⟨9015367960999295698020637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12020490614665727597360849 9015367960999295698020637)
          ·
            refine ⟨3380762985374735886757739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9015367960999295698020637 3380762985374735886757739)
            ·
              refine ⟨5071144478062103830136609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380762985374735886757739 5071144478062103830136609)
              ·
                refine ⟨3803358358546577872602457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5071144478062103830136609 3803358358546577872602457)
                ·
                  refine ⟨2852518768909933404451843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803358358546577872602457 2852518768909933404451843)
                  ·
                    refine ⟨4278778153364900106677765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852518768909933404451843 4278778153364900106677765)
                    ·
                      refine ⟨802270903755918770002081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4278778153364900106677765 802270903755918770002081)
                      ·
                        rfl

theorem cell23_1562417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1562417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562417 prefixEnd_1562417 := by exact prefixLift 1562417
  have htrace : WordTrace (prefixWord ++ tailWord_1562417) baseStart_1562417 baseEnd_1562417 := by
    simpa [prefixWord, tailWord_1562417, baseEnd_1562417] using wordTrace_append hprefix tailTrace_1562417
  have hstable : (prefixWord ++ tailWord_1562417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562417).length < 2 ^ (prefixWord ++ tailWord_1562417).sum := by decide
  have hdescent : baseEnd_1562417 < baseStart_1562417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562478 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_1562478 : Nat := 118140960795 + 1562478 * 2 ^ 59
def prefixEnd_1562478 : Nat := 4983230072969 + 3 ^ 40 * 1562478 * 2
def baseEnd_1562478 : Nat := 267434075358614343779767

theorem tailTrace_1562478 : CollatzResearch.WordTrace tailWord_1562478 prefixEnd_1562478 267434075358614343779767 := by
  unfold tailWord_1562478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123531804177066355312011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37992169622277687228330725 7123531804177066355312011)
  ·
    refine ⟨10685297706265599532968017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7123531804177066355312011 10685297706265599532968017)
    ·
      refine ⟨8013973279699199649726013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10685297706265599532968017 8013973279699199649726013)
      ·
        refine ⟨3005239979887199868647255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8013973279699199649726013 3005239979887199868647255)
        ·
          refine ⟨4507859969830799802970883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005239979887199868647255 4507859969830799802970883)
          ·
            refine ⟨6761789954746199704456325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507859969830799802970883 6761789954746199704456325)
            ·
              refine ⟨1267835616514912444585561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6761789954746199704456325 1267835616514912444585561)
              ·
                refine ⟨950876712386184333439171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267835616514912444585561 950876712386184333439171)
                ·
                  refine ⟨1426315068579276500158757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950876712386184333439171 1426315068579276500158757)
                  ·
                    refine ⟨267434075358614343779767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426315068579276500158757 267434075358614343779767)
                    ·
                      rfl

theorem cell23_1562478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_1562478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562478 prefixEnd_1562478 := by exact prefixLift 1562478
  have htrace : WordTrace (prefixWord ++ tailWord_1562478) baseStart_1562478 baseEnd_1562478 := by
    simpa [prefixWord, tailWord_1562478, baseEnd_1562478] using wordTrace_append hprefix tailTrace_1562478
  have hstable : (prefixWord ++ tailWord_1562478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562478).length < 2 ^ (prefixWord ++ tailWord_1562478).sum := by decide
  have hdescent : baseEnd_1562478 < baseStart_1562478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562507 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 4]
def baseStart_1562507 : Nat := 118140960795 + 1562507 * 2 ^ 59
def prefixEnd_1562507 : Nat := 4983230072969 + 3 ^ 40 * 1562507 * 2
def baseEnd_1562507 : Nat := 802317117014823417876667

theorem tailTrace_1562507 : CollatzResearch.WordTrace tailWord_1562507 prefixEnd_1562507 802317117014823417876667 := by
  unfold tailWord_1562507
  simp only [CollatzResearch.WordTrace]
  refine ⟨56989312150311468795301775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37992874766874312530201183 56989312150311468795301775)
  ·
    refine ⟨85483968225467203192952663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56989312150311468795301775 85483968225467203192952663)
    ·
      refine ⟨128225952338200804789428995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85483968225467203192952663 128225952338200804789428995)
      ·
        refine ⟨192338928507301207184143493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128225952338200804789428995 192338928507301207184143493)
        ·
          refine ⟨36063549095118976347026905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192338928507301207184143493 36063549095118976347026905)
          ·
            refine ⟨27047661821339232260270179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36063549095118976347026905 27047661821339232260270179)
            ·
              refine ⟨40571492732008848390405269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27047661821339232260270179 40571492732008848390405269)
              ·
                refine ⟨1901788721812914768300247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40571492732008848390405269 1901788721812914768300247)
                ·
                  refine ⟨2852683082719372152450371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901788721812914768300247 2852683082719372152450371)
                  ·
                    refine ⟨4279024624079058228675557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852683082719372152450371 4279024624079058228675557)
                    ·
                      refine ⟨802317117014823417876667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4279024624079058228675557 802317117014823417876667)
                      ·
                        rfl

theorem cell23_1562507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 4].length) (baseStart_1562507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562507 prefixEnd_1562507 := by exact prefixLift 1562507
  have htrace : WordTrace (prefixWord ++ tailWord_1562507) baseStart_1562507 baseEnd_1562507 := by
    simpa [prefixWord, tailWord_1562507, baseEnd_1562507] using wordTrace_append hprefix tailTrace_1562507
  have hstable : (prefixWord ++ tailWord_1562507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562507).length < 2 ^ (prefixWord ++ tailWord_1562507).sum := by decide
  have hdescent : baseEnd_1562507 < baseStart_1562507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562517 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1562517 : Nat := 118140960795 + 1562517 * 2 ^ 59
def prefixEnd_1562517 : Nat := 4983230072969 + 3 ^ 40 * 1562517 * 2
def baseEnd_1562517 : Nat := 267440750607122792917207

theorem tailTrace_1562517 : CollatzResearch.WordTrace tailWord_1562517 prefixEnd_1562517 267440750607122792917207 := by
  unfold tailWord_1562517
  simp only [CollatzResearch.WordTrace]
  refine ⟨56989676880275240503165805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37993117920183493668777203 56989676880275240503165805)
  ·
    refine ⟨21371128830103215188687177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56989676880275240503165805 21371128830103215188687177)
    ·
      refine ⟨16028346622577411391515383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21371128830103215188687177 16028346622577411391515383)
      ·
        refine ⟨24042519933866117087273075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16028346622577411391515383 24042519933866117087273075)
        ·
          refine ⟨36063779900799175630909613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24042519933866117087273075 36063779900799175630909613)
          ·
            refine ⟨13523917462799690861591105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36063779900799175630909613 13523917462799690861591105)
            ·
              refine ⟨10142938097099768146193329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13523917462799690861591105 10142938097099768146193329)
              ·
                refine ⟨7607203572824826109644997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10142938097099768146193329 7607203572824826109644997)
                ·
                  refine ⟨1426350669904654895558437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7607203572824826109644997 1426350669904654895558437)
                  ·
                    refine ⟨267440750607122792917207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426350669904654895558437 267440750607122792917207)
                    ·
                      rfl

theorem cell23_1562517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1562517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562517 prefixEnd_1562517 := by exact prefixLift 1562517
  have htrace : WordTrace (prefixWord ++ tailWord_1562517) baseStart_1562517 baseEnd_1562517 := by
    simpa [prefixWord, tailWord_1562517, baseEnd_1562517] using wordTrace_append hprefix tailTrace_1562517
  have hstable : (prefixWord ++ tailWord_1562517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562517).length < 2 ^ (prefixWord ++ tailWord_1562517).sum := by decide
  have hdescent : baseEnd_1562517 < baseStart_1562517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562574 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_1562574 : Nat := 118140960795 + 1562574 * 2 ^ 59
def prefixEnd_1562574 : Nat := 4983230072969 + 3 ^ 40 * 1562574 * 2
def baseEnd_1562574 : Nat := 802351520218674655738859

theorem tailTrace_1562574 : CollatzResearch.WordTrace tailWord_1562574 prefixEnd_1562574 802351520218674655738859 := by
  unfold tailWord_1562574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123969480133592404748847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37994503894045826158660517 7123969480133592404748847)
  ·
    refine ⟨10685954220200388607123271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7123969480133592404748847 10685954220200388607123271)
    ·
      refine ⟨16028931330300582910684907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10685954220200388607123271 16028931330300582910684907)
      ·
        refine ⟨24043396995450874366027361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16028931330300582910684907 24043396995450874366027361)
        ·
          refine ⟨18032547746588155774520521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24043396995450874366027361 18032547746588155774520521)
          ·
            refine ⟨13524410809941116830890391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18032547746588155774520521 13524410809941116830890391)
            ·
              refine ⟨20286616214911675246335587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13524410809941116830890391 20286616214911675246335587)
              ·
                refine ⟨30429924322367512869503381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20286616214911675246335587 30429924322367512869503381)
                ·
                  refine ⟨1426402702610977165757971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30429924322367512869503381 1426402702610977165757971)
                  ·
                    refine ⟨2139604053916465748636957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1426402702610977165757971 2139604053916465748636957)
                    ·
                      refine ⟨802351520218674655738859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2139604053916465748636957 802351520218674655738859)
                      ·
                        rfl

theorem cell23_1562574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_1562574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562574 prefixEnd_1562574 := by exact prefixLift 1562574
  have htrace : WordTrace (prefixWord ++ tailWord_1562574) baseStart_1562574 baseEnd_1562574 := by
    simpa [prefixWord, tailWord_1562574, baseEnd_1562574] using wordTrace_append hprefix tailTrace_1562574
  have hstable : (prefixWord ++ tailWord_1562574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562574).length < 2 ^ (prefixWord ++ tailWord_1562574).sum := by decide
  have hdescent : baseEnd_1562574 < baseStart_1562574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562617 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1562617 : Nat := 118140960795 + 1562617 * 2 ^ 59
def prefixEnd_1562617 : Nat := 4983230072969 + 3 ^ 40 * 1562617 * 2
def baseEnd_1562617 : Nat := 802373599886817987501161

theorem tailTrace_1562617 : CollatzResearch.WordTrace tailWord_1562617 prefixEnd_1562617 802373599886817987501161 := by
  unfold tailWord_1562617
  simp only [CollatzResearch.WordTrace]
  refine ⟨56993324179912957581806105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37995549453275305054537403 56993324179912957581806105)
  ·
    refine ⟨42744993134934718186354579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56993324179912957581806105 42744993134934718186354579)
    ·
      refine ⟨64117489702402077279531869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42744993134934718186354579 64117489702402077279531869)
      ·
        refine ⟨24044058638400778979824451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64117489702402077279531869 24044058638400778979824451)
        ·
          refine ⟨36066087957601168469736677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24044058638400778979824451 36066087957601168469736677)
          ·
            refine ⟨6762391492050219088075627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36066087957601168469736677 6762391492050219088075627)
            ·
              refine ⟨10143587238075328632113441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762391492050219088075627 10143587238075328632113441)
              ·
                refine ⟨7607690428556496474085081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10143587238075328632113441 7607690428556496474085081)
                ·
                  refine ⟨5705767821417372355563811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7607690428556496474085081 5705767821417372355563811)
                  ·
                    refine ⟨8558651732126058533345717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705767821417372355563811 8558651732126058533345717)
                    ·
                      refine ⟨802373599886817987501161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8558651732126058533345717 802373599886817987501161)
                      ·
                        rfl

theorem cell23_1562617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1562617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562617 prefixEnd_1562617 := by exact prefixLift 1562617
  have htrace : WordTrace (prefixWord ++ tailWord_1562617) baseStart_1562617 baseEnd_1562617 := by
    simpa [prefixWord, tailWord_1562617, baseEnd_1562617] using wordTrace_append hprefix tailTrace_1562617
  have hstable : (prefixWord ++ tailWord_1562617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562617).length < 2 ^ (prefixWord ++ tailWord_1562617).sum := by decide
  have hdescent : baseEnd_1562617 < baseStart_1562617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562631 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_1562631 : Nat := 118140960795 + 1562631 * 2 ^ 59
def prefixEnd_1562631 : Nat := 4983230072969 + 3 ^ 40 * 1562631 * 2
def baseEnd_1562631 : Nat := 802380788615980932726097

theorem tailTrace_1562631 : CollatzResearch.WordTrace tailWord_1562631 prefixEnd_1562631 802380788615980932726097 := by
  unfold tailWord_1562631
  simp only [CollatzResearch.WordTrace]
  refine ⟨56993834801862237972815747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37995889867908158648543831 56993834801862237972815747)
  ·
    refine ⟨85490752202793356959223621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56993834801862237972815747 85490752202793356959223621)
    ·
      refine ⟨16029516038023754429854429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85490752202793356959223621 16029516038023754429854429)
      ·
        refine ⟨6011068514258907911195411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16029516038023754429854429 6011068514258907911195411)
        ·
          refine ⟨9016602771388361866793117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011068514258907911195411 9016602771388361866793117)
          ·
            refine ⟨3381226039270635700047419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9016602771388361866793117 3381226039270635700047419)
            ·
              refine ⟨5071839058905953550071129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381226039270635700047419 5071839058905953550071129)
              ·
                refine ⟨3803879294179465162553347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5071839058905953550071129 3803879294179465162553347)
                ·
                  refine ⟨5705818941269197743830021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803879294179465162553347 5705818941269197743830021)
                  ·
                    refine ⟨1069841051487974576968129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5705818941269197743830021 1069841051487974576968129)
                    ·
                      refine ⟨802380788615980932726097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069841051487974576968129 802380788615980932726097)
                      ·
                        rfl

theorem cell23_1562631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_1562631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562631 prefixEnd_1562631 := by exact prefixLift 1562631
  have htrace : WordTrace (prefixWord ++ tailWord_1562631) baseStart_1562631 baseEnd_1562631 := by
    simpa [prefixWord, tailWord_1562631, baseEnd_1562631] using wordTrace_append hprefix tailTrace_1562631
  have hstable : (prefixWord ++ tailWord_1562631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562631).length < 2 ^ (prefixWord ++ tailWord_1562631).sum := by decide
  have hdescent : baseEnd_1562631 < baseStart_1562631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562648 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 2, 2, 2]
def baseStart_1562648 : Nat := 118140960795 + 1562648 * 2 ^ 59
def prefixEnd_1562648 : Nat := 4983230072969 + 3 ^ 40 * 1562648 * 2
def baseEnd_1562648 : Nat := 802389517787107366213519

theorem tailTrace_1562648 : CollatzResearch.WordTrace tailWord_1562648 prefixEnd_1562648 802389517787107366213519 := by
  unfold tailWord_1562648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28497227421400324938092299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37996303228533766584123065 28497227421400324938092299)
  ·
    refine ⟨42745841132100487407138449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28497227421400324938092299 42745841132100487407138449)
    ·
      refine ⟨32059380849075365555353837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42745841132100487407138449 32059380849075365555353837)
      ·
        refine ⟨12022267818403262083257689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32059380849075365555353837 12022267818403262083257689)
        ·
          refine ⟨9016700863802446562443267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12022267818403262083257689 9016700863802446562443267)
          ·
            refine ⟨13525051295703669843664901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9016700863802446562443267 13525051295703669843664901)
            ·
              refine ⟨2535947117944438095687169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13525051295703669843664901 2535947117944438095687169)
              ·
                refine ⟨1901960338458328571765377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535947117944438095687169 1901960338458328571765377)
                ·
                  refine ⟨1426470253843746428824033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901960338458328571765377 1426470253843746428824033)
                  ·
                    refine ⟨1069852690382809821618025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1426470253843746428824033 1069852690382809821618025)
                    ·
                      refine ⟨802389517787107366213519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069852690382809821618025 802389517787107366213519)
                      ·
                        rfl

theorem cell23_1562648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_1562648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562648 prefixEnd_1562648 := by exact prefixLift 1562648
  have htrace : WordTrace (prefixWord ++ tailWord_1562648) baseStart_1562648 baseEnd_1562648 := by
    simpa [prefixWord, tailWord_1562648, baseEnd_1562648] using wordTrace_append hprefix tailTrace_1562648
  have hstable : (prefixWord ++ tailWord_1562648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562648).length < 2 ^ (prefixWord ++ tailWord_1562648).sum := by decide
  have hdescent : baseEnd_1562648 < baseStart_1562648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562677 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1562677 : Nat := 118140960795 + 1562677 * 2 ^ 59
def prefixEnd_1562677 : Nat := 4983230072969 + 3 ^ 40 * 1562677 * 2
def baseEnd_1562677 : Nat := 802404408726087752750885

theorem tailTrace_1562677 : CollatzResearch.WordTrace tailWord_1562677 prefixEnd_1562677 802404408726087752750885 := by
  unfold tailWord_1562677
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995512559695587828990285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37997008373130391885993523 56995512559695587828990285)
  ·
    refine ⟨21373317209885845435871357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56995512559695587828990285 21373317209885845435871357)
    ·
      refine ⟨8014993953707192038451759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21373317209885845435871357 8014993953707192038451759)
      ·
        refine ⟨12022490930560788057677639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014993953707192038451759 12022490930560788057677639)
        ·
          refine ⟨18033736395841182086516459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12022490930560788057677639 18033736395841182086516459)
          ·
            refine ⟨27050604593761773129774689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033736395841182086516459 27050604593761773129774689)
            ·
              refine ⟨20287953445321329847331017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27050604593761773129774689 20287953445321329847331017)
              ·
                refine ⟨15215965083990997385498263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20287953445321329847331017 15215965083990997385498263)
                ·
                  refine ⟨22823947625986496078247395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15215965083990997385498263 22823947625986496078247395)
                  ·
                    refine ⟨34235921438979744117371093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22823947625986496078247395 34235921438979744117371093)
                    ·
                      refine ⟨802404408726087752750885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34235921438979744117371093 802404408726087752750885)
                      ·
                        rfl

theorem cell23_1562677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1562677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562677 prefixEnd_1562677 := by exact prefixLift 1562677
  have htrace : WordTrace (prefixWord ++ tailWord_1562677) baseStart_1562677 baseEnd_1562677 := by
    simpa [prefixWord, tailWord_1562677, baseEnd_1562677] using wordTrace_append hprefix tailTrace_1562677
  have hstable : (prefixWord ++ tailWord_1562677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562677).length < 2 ^ (prefixWord ++ tailWord_1562677).sum := by decide
  have hdescent : baseEnd_1562677 < baseStart_1562677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562724 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_1562724 : Nat := 118140960795 + 1562724 * 2 ^ 59
def prefixEnd_1562724 : Nat := 4983230072969 + 3 ^ 40 * 1562724 * 2
def baseEnd_1562724 : Nat := 802428542316849068863169

theorem tailTrace_1562724 : CollatzResearch.WordTrace tailWord_1562724 prefixEnd_1562724 802428542316849068863169 := by
  unfold tailWord_1562724
  simp only [CollatzResearch.WordTrace]
  refine ⟨28498613395262657427975613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37998151193683543237300817 28498613395262657427975613)
  ·
    refine ⟨10686980023223496535490855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28498613395262657427975613 10686980023223496535490855)
    ·
      refine ⟨16030470034835244803236283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10686980023223496535490855 16030470034835244803236283)
      ·
        refine ⟨24045705052252867204854425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16030470034835244803236283 24045705052252867204854425)
        ·
          refine ⟨18034278789189650403640819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24045705052252867204854425 18034278789189650403640819)
          ·
            refine ⟨27051418183784475605461229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18034278789189650403640819 27051418183784475605461229)
            ·
              refine ⟨10144281818919178352047961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27051418183784475605461229 10144281818919178352047961)
              ·
                refine ⟨7608211364189383764035971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10144281818919178352047961 7608211364189383764035971)
                ·
                  refine ⟨11412317046284075646053957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7608211364189383764035971 11412317046284075646053957)
                  ·
                    refine ⟨2139809446178264183635117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11412317046284075646053957 2139809446178264183635117)
                    ·
                      refine ⟨802428542316849068863169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2139809446178264183635117 802428542316849068863169)
                      ·
                        rfl

theorem cell23_1562724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_1562724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562724 prefixEnd_1562724 := by exact prefixLift 1562724
  have htrace : WordTrace (prefixWord ++ tailWord_1562724) baseStart_1562724 baseEnd_1562724 := by
    simpa [prefixWord, tailWord_1562724, baseEnd_1562724] using wordTrace_append hprefix tailTrace_1562724
  have hstable : (prefixWord ++ tailWord_1562724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562724).length < 2 ^ (prefixWord ++ tailWord_1562724).sum := by decide
  have hdescent : baseEnd_1562724 < baseStart_1562724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562734 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1562734 : Nat := 118140960795 + 1562734 * 2 ^ 59
def prefixEnd_1562734 : Nat := 4983230072969 + 3 ^ 40 * 1562734 * 2
def baseEnd_1562734 : Nat := 802433677123394029738123

theorem tailTrace_1562734 : CollatzResearch.WordTrace tailWord_1562734 prefixEnd_1562734 802433677123394029738123 := by
  unfold tailWord_1562734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7124698940061135820476907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37998394346992724375876837 7124698940061135820476907)
  ·
    refine ⟨10687048410091703730715361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7124698940061135820476907 10687048410091703730715361)
    ·
      refine ⟨8015286307568777798036521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10687048410091703730715361 8015286307568777798036521)
      ·
        refine ⟨6011464730676583348527391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8015286307568777798036521 6011464730676583348527391)
        ·
          refine ⟨9017197096014875022791087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011464730676583348527391 9017197096014875022791087)
          ·
            refine ⟨13525795644022312534186631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017197096014875022791087 13525795644022312534186631)
            ·
              refine ⟨20288693466033468801279947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13525795644022312534186631 20288693466033468801279947)
              ·
                refine ⟨30433040199050203201919921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20288693466033468801279947 30433040199050203201919921)
                ·
                  refine ⟨22824780149287652401439941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30433040199050203201919921 22824780149287652401439941)
                  ·
                    refine ⟨4279646277991434825269989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22824780149287652401439941 4279646277991434825269989)
                    ·
                      refine ⟨802433677123394029738123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4279646277991434825269989 802433677123394029738123)
                      ·
                        rfl

theorem cell23_1562734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1562734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562734 prefixEnd_1562734 := by exact prefixLift 1562734
  have htrace : WordTrace (prefixWord ++ tailWord_1562734) baseStart_1562734 baseEnd_1562734 := by
    simpa [prefixWord, tailWord_1562734, baseEnd_1562734] using wordTrace_append hprefix tailTrace_1562734
  have hstable : (prefixWord ++ tailWord_1562734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562734).length < 2 ^ (prefixWord ++ tailWord_1562734).sum := by decide
  have hdescent : baseEnd_1562734 < baseStart_1562734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562748 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_1562748 : Nat := 118140960795 + 1562748 * 2 ^ 59
def prefixEnd_1562748 : Nat := 4983230072969 + 3 ^ 40 * 1562748 * 2
def baseEnd_1562748 : Nat := 267480288617518991654353

theorem tailTrace_1562748 : CollatzResearch.WordTrace tailWord_1562748 prefixEnd_1562748 267480288617518991654353 := by
  unfold tailWord_1562748
  simp only [CollatzResearch.WordTrace]
  refine ⟨28499051071219183477412449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37998734761625577969883265 28499051071219183477412449)
  ·
    refine ⟨21374288303414387608059337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28499051071219183477412449 21374288303414387608059337)
    ·
      refine ⟨16030716227560790706044503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21374288303414387608059337 16030716227560790706044503)
      ·
        refine ⟨24046074341341186059066755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16030716227560790706044503 24046074341341186059066755)
        ·
          refine ⟨36069111512011779088600133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24046074341341186059066755 36069111512011779088600133)
          ·
            refine ⟨6762958408502208579112525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36069111512011779088600133 6762958408502208579112525)
            ·
              refine ⟨2536109403188328217167197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6762958408502208579112525 2536109403188328217167197)
              ·
                refine ⟨951041026195623081437699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2536109403188328217167197 951041026195623081437699)
                ·
                  refine ⟨1426561539293434622156549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951041026195623081437699 1426561539293434622156549)
                  ·
                    refine ⟨267480288617518991654353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426561539293434622156549 267480288617518991654353)
                    ·
                      rfl

theorem cell23_1562748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_1562748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562748 prefixEnd_1562748 := by exact prefixLift 1562748
  have htrace : WordTrace (prefixWord ++ tailWord_1562748) baseStart_1562748 baseEnd_1562748 := by
    simpa [prefixWord, tailWord_1562748, baseEnd_1562748] using wordTrace_append hprefix tailTrace_1562748
  have hstable : (prefixWord ++ tailWord_1562748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562748).length < 2 ^ (prefixWord ++ tailWord_1562748).sum := by decide
  have hdescent : baseEnd_1562748 < baseStart_1562748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562821 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_1562821 : Nat := 118140960795 + 1562821 * 2 ^ 59
def prefixEnd_1562821 : Nat := 4983230072969 + 3 ^ 40 * 1562821 * 2
def baseEnd_1562821 : Nat := 267492783313445063116741

theorem tailTrace_1562821 : CollatzResearch.WordTrace tailWord_1562821 prefixEnd_1562821 267492783313445063116741 := by
  unfold tailWord_1562821
  simp only [CollatzResearch.WordTrace]
  refine ⟨57000764671173900422232317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38000509780782600281488211 57000764671173900422232317)
  ·
    refine ⟨21375286751690212658337119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57000764671173900422232317 21375286751690212658337119)
    ·
      refine ⟨32062930127535318987505679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21375286751690212658337119 32062930127535318987505679)
      ·
        refine ⟨48094395191302978481258519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32062930127535318987505679 48094395191302978481258519)
        ·
          refine ⟨72141592786954467721887779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48094395191302978481258519 72141592786954467721887779)
          ·
            refine ⟨108212389180431701582831669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72141592786954467721887779 108212389180431701582831669)
            ·
              refine ⟨10144911485665472023390469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108212389180431701582831669 10144911485665472023390469)
              ·
                refine ⟨1902170903562276004385713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10144911485665472023390469 1902170903562276004385713)
                ·
                  refine ⟨1426628177671707003289285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1902170903562276004385713 1426628177671707003289285)
                  ·
                    refine ⟨267492783313445063116741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426628177671707003289285 267492783313445063116741)
                    ·
                      rfl

theorem cell23_1562821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_1562821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562821 prefixEnd_1562821 := by exact prefixLift 1562821
  have htrace : WordTrace (prefixWord ++ tailWord_1562821) baseStart_1562821 baseEnd_1562821 := by
    simpa [prefixWord, tailWord_1562821, baseEnd_1562821] using wordTrace_append hprefix tailTrace_1562821
  have hstable : (prefixWord ++ tailWord_1562821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562821).length < 2 ^ (prefixWord ++ tailWord_1562821).sum := by decide
  have hdescent : baseEnd_1562821 < baseStart_1562821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562824 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1562824 : Nat := 118140960795 + 1562824 * 2 ^ 59
def prefixEnd_1562824 : Nat := 4983230072969 + 3 ^ 40 * 1562824 * 2
def baseEnd_1562824 : Nat := 802479890382298677612709

theorem tailTrace_1562824 : CollatzResearch.WordTrace tailWord_1562824 prefixEnd_1562824 802479890382298677612709 := by
  unfold tailWord_1562824
  simp only [CollatzResearch.WordTrace]
  refine ⟨28500437045081515967295763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38000582726775354623061017 28500437045081515967295763)
  ·
    refine ⟨42750655567622273950943645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28500437045081515967295763 42750655567622273950943645)
    ·
      refine ⟨16031495837858352731603867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42750655567622273950943645 16031495837858352731603867)
      ·
        refine ⟨24047243756787529097405801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16031495837858352731603867 24047243756787529097405801)
        ·
          refine ⟨18035432817590646823054351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24047243756787529097405801 18035432817590646823054351)
          ·
            refine ⟨27053149226385970234581527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18035432817590646823054351 27053149226385970234581527)
            ·
              refine ⟨40579723839578955351872291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27053149226385970234581527 40579723839578955351872291)
              ·
                refine ⟨60869585759368433027808437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40579723839578955351872291 60869585759368433027808437)
                ·
                  refine ⟨5706523664940790596357041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60869585759368433027808437 5706523664940790596357041)
                  ·
                    refine ⟨4279892748705592947267781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5706523664940790596357041 4279892748705592947267781)
                    ·
                      refine ⟨802479890382298677612709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4279892748705592947267781 802479890382298677612709)
                      ·
                        rfl

theorem cell23_1562824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1562824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562824 prefixEnd_1562824 := by exact prefixLift 1562824
  have htrace : WordTrace (prefixWord ++ tailWord_1562824) baseStart_1562824 baseEnd_1562824 := by
    simpa [prefixWord, tailWord_1562824, baseEnd_1562824] using wordTrace_append hprefix tailTrace_1562824
  have hstable : (prefixWord ++ tailWord_1562824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562824).length < 2 ^ (prefixWord ++ tailWord_1562824).sum := by decide
  have hdescent : baseEnd_1562824 < baseStart_1562824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562838 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1562838 : Nat := 118140960795 + 1562838 * 2 ^ 59
def prefixEnd_1562838 : Nat := 4983230072969 + 3 ^ 40 * 1562838 * 2
def baseEnd_1562838 : Nat := 267495693037153874279215

theorem tailTrace_1562838 : CollatzResearch.WordTrace tailWord_1562838 prefixEnd_1562838 267495693037153874279215 := by
  unfold tailWord_1562838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562586544507019520350073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38000923141408208217067445 3562586544507019520350073)
  ·
    refine ⟨2671939908380264640262555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3562586544507019520350073 2671939908380264640262555)
    ·
      refine ⟨4007909862570396960393833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671939908380264640262555 4007909862570396960393833)
      ·
        refine ⟨3005932396927797720295375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007909862570396960393833 3005932396927797720295375)
        ·
          refine ⟨4508898595391696580443063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005932396927797720295375 4508898595391696580443063)
          ·
            refine ⟨6763347893087544870664595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508898595391696580443063 6763347893087544870664595)
            ·
              refine ⟨10145021839631317305996893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763347893087544870664595 10145021839631317305996893)
              ·
                refine ⟨3804383189861743989748835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10145021839631317305996893 3804383189861743989748835)
                ·
                  refine ⟨5706574784792615984623253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804383189861743989748835 5706574784792615984623253)
                  ·
                    refine ⟨267495693037153874279215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5706574784792615984623253 267495693037153874279215)
                    ·
                      rfl

theorem cell23_1562838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1562838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562838 prefixEnd_1562838 := by exact prefixLift 1562838
  have htrace : WordTrace (prefixWord ++ tailWord_1562838) baseStart_1562838 baseEnd_1562838 := by
    simpa [prefixWord, tailWord_1562838, baseEnd_1562838] using wordTrace_append hprefix tailTrace_1562838
  have hstable : (prefixWord ++ tailWord_1562838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562838).length < 2 ^ (prefixWord ++ tailWord_1562838).sum := by decide
  have hdescent : baseEnd_1562838 < baseStart_1562838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562845 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1562845 : Nat := 118140960795 + 1562845 * 2 ^ 59
def prefixEnd_1562845 : Nat := 4983230072969 + 3 ^ 40 * 1562845 * 2
def baseEnd_1562845 : Nat := 802490673476043095450113

theorem tailTrace_1562845 : CollatzResearch.WordTrace tailWord_1562845 prefixEnd_1562845 802490673476043095450113 := by
  unfold tailWord_1562845
  simp only [CollatzResearch.WordTrace]
  refine ⟨57001640023086952521105989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38001093348724635014070659 57001640023086952521105989)
  ·
    refine ⟨10687807504328803597707373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57001640023086952521105989 10687807504328803597707373)
    ·
      refine ⟨4007927814123301349140265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10687807504328803597707373 4007927814123301349140265)
      ·
        refine ⟨3005945860592476011855199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007927814123301349140265 3005945860592476011855199)
        ·
          refine ⟨4508918790888714017782799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005945860592476011855199 4508918790888714017782799)
          ·
            refine ⟨6763378186333071026674199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508918790888714017782799 6763378186333071026674199)
            ·
              refine ⟨10145067279499606540011299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763378186333071026674199 10145067279499606540011299)
              ·
                refine ⟨15217600919249409810016949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145067279499606540011299 15217600919249409810016949)
                ·
                  refine ⟨1426650086179632169689089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15217600919249409810016949 1426650086179632169689089)
                  ·
                    refine ⟨1069987564634724127266817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1426650086179632169689089 1069987564634724127266817)
                    ·
                      refine ⟨802490673476043095450113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1069987564634724127266817 802490673476043095450113)
                      ·
                        rfl

theorem cell23_1562845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1562845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562845 prefixEnd_1562845 := by exact prefixLift 1562845
  have htrace : WordTrace (prefixWord ++ tailWord_1562845) baseStart_1562845 baseEnd_1562845 := by
    simpa [prefixWord, tailWord_1562845, baseEnd_1562845] using wordTrace_append hprefix tailTrace_1562845
  have hstable : (prefixWord ++ tailWord_1562845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562845).length < 2 ^ (prefixWord ++ tailWord_1562845).sum := by decide
  have hdescent : baseEnd_1562845 < baseStart_1562845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562924 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 9]
def baseStart_1562924 : Nat := 118140960795 + 1562924 * 2 ^ 59
def prefixEnd_1562924 : Nat := 4983230072969 + 3 ^ 40 * 1562924 * 2
def baseEnd_1562924 : Nat := 89170137605305365151361

theorem tailTrace_1562924 : CollatzResearch.WordTrace tailWord_1562924 prefixEnd_1562924 89170137605305365151361 := by
  unfold tailWord_1562924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28502260694900374506615913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38003014259867166008821217 28502260694900374506615913)
  ·
    refine ⟨21376695521175280879961935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28502260694900374506615913 21376695521175280879961935)
    ·
      refine ⟨32065043281762921319942903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21376695521175280879961935 32065043281762921319942903)
      ·
        refine ⟨48097564922644381979914355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32065043281762921319942903 48097564922644381979914355)
        ·
          refine ⟨72146347383966572969871533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48097564922644381979914355 72146347383966572969871533)
          ·
            refine ⟨27054880268987464863701825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72146347383966572969871533 27054880268987464863701825)
            ·
              refine ⟨20291160201740598647776369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27054880268987464863701825 20291160201740598647776369)
              ·
                refine ⟨15218370151305448985832277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20291160201740598647776369 15218370151305448985832277)
                ·
                  refine ⟨89170137605305365151361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15218370151305448985832277 89170137605305365151361)
                  ·
                    rfl

theorem cell23_1562924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_1562924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562924 prefixEnd_1562924 := by exact prefixLift 1562924
  have htrace : WordTrace (prefixWord ++ tailWord_1562924) baseStart_1562924 baseEnd_1562924 := by
    simpa [prefixWord, tailWord_1562924, baseEnd_1562924] using wordTrace_append hprefix tailTrace_1562924
  have hstable : (prefixWord ++ tailWord_1562924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562924).length < 2 ^ (prefixWord ++ tailWord_1562924).sum := by decide
  have hdescent : baseEnd_1562924 < baseStart_1562924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562944 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1562944 : Nat := 118140960795 + 1562944 * 2 ^ 59
def prefixEnd_1562944 : Nat := 4983230072969 + 3 ^ 40 * 1562944 * 2
def baseEnd_1562944 : Nat := 802541508060838208112157

theorem tailTrace_1562944 : CollatzResearch.WordTrace tailWord_1562944 prefixEnd_1562944 802541508060838208112157 := by
  unfold tailWord_1562944
  simp only [CollatzResearch.WordTrace]
  refine ⟨28502625424864146214479943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38003500566485528285973257 28502625424864146214479943)
  ·
    refine ⟨42753938137296219321719915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28502625424864146214479943 42753938137296219321719915)
    ·
      refine ⟨64130907205944328982579873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42753938137296219321719915 64130907205944328982579873)
      ·
        refine ⟨48098180404458246736934905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64130907205944328982579873 48098180404458246736934905)
        ·
          refine ⟨36073635303343685052701179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48098180404458246736934905 36073635303343685052701179)
          ·
            refine ⟨54110452955015527579051769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36073635303343685052701179 54110452955015527579051769)
            ·
              refine ⟨40582839716261645684288827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54110452955015527579051769 40582839716261645684288827)
              ·
                refine ⟨60874259574392468526433241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40582839716261645684288827 60874259574392468526433241)
                ·
                  refine ⟨45655694680794351394824931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60874259574392468526433241 45655694680794351394824931)
                  ·
                    refine ⟨68483542021191527092237397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45655694680794351394824931 68483542021191527092237397)
                    ·
                      refine ⟨802541508060838208112157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68483542021191527092237397 802541508060838208112157)
                      ·
                        rfl

theorem cell23_1562944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1562944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562944 prefixEnd_1562944 := by exact prefixLift 1562944
  have htrace : WordTrace (prefixWord ++ tailWord_1562944) baseStart_1562944 baseEnd_1562944 := by
    simpa [prefixWord, tailWord_1562944, baseEnd_1562944] using wordTrace_append hprefix tailTrace_1562944
  have hstable : (prefixWord ++ tailWord_1562944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562944).length < 2 ^ (prefixWord ++ tailWord_1562944).sum := by decide
  have hdescent : baseEnd_1562944 < baseStart_1562944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562951 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_1562951 : Nat := 118140960795 + 1562951 * 2 ^ 59
def prefixEnd_1562951 : Nat := 4983230072969 + 3 ^ 40 * 1562951 * 2
def baseEnd_1562951 : Nat := 802545102425419680724625

theorem tailTrace_1562951 : CollatzResearch.WordTrace tailWord_1562951 prefixEnd_1562951 802545102425419680724625 := by
  unfold tailWord_1562951
  simp only [CollatzResearch.WordTrace]
  refine ⟨57005506160702932624464707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38003670773801955082976471 57005506160702932624464707)
  ·
    refine ⟨85508259241054398936697061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57005506160702932624464707 85508259241054398936697061)
    ·
      refine ⟨16032798607697699800630699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85508259241054398936697061 16032798607697699800630699)
      ·
        refine ⟨24049197911546549700946049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16032798607697699800630699 24049197911546549700946049)
        ·
          refine ⟨18036898433659912275709537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24049197911546549700946049 18036898433659912275709537)
          ·
            refine ⟨13527673825244934206782153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18036898433659912275709537 13527673825244934206782153)
            ·
              refine ⟨10145755368933700655086615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13527673825244934206782153 10145755368933700655086615)
              ·
                refine ⟨15218633053400550982629923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145755368933700655086615 15218633053400550982629923)
                ·
                  refine ⟨22827949580100826473944885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15218633053400550982629923 22827949580100826473944885)
                  ·
                    refine ⟨2140120273134452481932333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22827949580100826473944885 2140120273134452481932333)
                    ·
                      refine ⟨802545102425419680724625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2140120273134452481932333 802545102425419680724625)
                      ·
                        rfl

theorem cell23_1562951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_1562951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562951 prefixEnd_1562951 := by exact prefixLift 1562951
  have htrace : WordTrace (prefixWord ++ tailWord_1562951) baseStart_1562951 baseEnd_1562951 := by
    simpa [prefixWord, tailWord_1562951, baseEnd_1562951] using wordTrace_append hprefix tailTrace_1562951
  have hstable : (prefixWord ++ tailWord_1562951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562951).length < 2 ^ (prefixWord ++ tailWord_1562951).sum := by decide
  have hdescent : baseEnd_1562951 < baseStart_1562951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562952 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_1562952 : Nat := 118140960795 + 1562952 * 2 ^ 59
def prefixEnd_1562952 : Nat := 4983230072969 + 3 ^ 40 * 1562952 * 2
def baseEnd_1562952 : Nat := 802545615906074176812121

theorem tailTrace_1562952 : CollatzResearch.WordTrace tailWord_1562952 prefixEnd_1562952 802545615906074176812121 := by
  unfold tailWord_1562952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28502771316849654897625555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38003695089132873196834073 28502771316849654897625555)
  ·
    refine ⟨42754156975274482346438333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28502771316849654897625555 42754156975274482346438333)
    ·
      refine ⟨16032808865727930879914375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42754156975274482346438333 16032808865727930879914375)
      ·
        refine ⟨24049213298591896319871563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16032808865727930879914375 24049213298591896319871563)
        ·
          refine ⟨36073819947887844479807345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24049213298591896319871563 36073819947887844479807345)
          ·
            refine ⟨27055364960915883359855509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36073819947887844479807345 27055364960915883359855509)
            ·
              refine ⟨1268220232542932032493227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27055364960915883359855509 1268220232542932032493227)
              ·
                refine ⟨1902330348814398048739841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268220232542932032493227 1902330348814398048739841)
                ·
                  refine ⟨1426747761610798536554881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1902330348814398048739841 1426747761610798536554881)
                  ·
                    refine ⟨1070060821208098902416161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1426747761610798536554881 1070060821208098902416161)
                    ·
                      refine ⟨802545615906074176812121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070060821208098902416161 802545615906074176812121)
                      ·
                        rfl

theorem cell23_1562952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_1562952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562952 prefixEnd_1562952 := by exact prefixLift 1562952
  have htrace : WordTrace (prefixWord ++ tailWord_1562952) baseStart_1562952 baseEnd_1562952 := by
    simpa [prefixWord, tailWord_1562952, baseEnd_1562952] using wordTrace_append hprefix tailTrace_1562952
  have hstable : (prefixWord ++ tailWord_1562952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562952).length < 2 ^ (prefixWord ++ tailWord_1562952).sum := by decide
  have hdescent : baseEnd_1562952 < baseStart_1562952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562981 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1562981 : Nat := 118140960795 + 1562981 * 2 ^ 59
def prefixEnd_1562981 : Nat := 4983230072969 + 3 ^ 40 * 1562981 * 2
def baseEnd_1562981 : Nat := 802560506845054563349487

theorem tailTrace_1562981 : CollatzResearch.WordTrace tailWord_1562981 prefixEnd_1562981 802560506845054563349487 := by
  unfold tailWord_1562981
  simp only [CollatzResearch.WordTrace]
  refine ⟨57006600350594247748056797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38004400233729498498704531 57006600350594247748056797)
  ·
    refine ⟨21377475131472842905521299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57006600350594247748056797 21377475131472842905521299)
    ·
      refine ⟨32066212697209264358281949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21377475131472842905521299 32066212697209264358281949)
      ·
        refine ⟨12024829761453474134355731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32066212697209264358281949 12024829761453474134355731)
        ·
          refine ⟨18037244642180211201533597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12024829761453474134355731 18037244642180211201533597)
          ·
            refine ⟨6763966740817579200575099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18037244642180211201533597 6763966740817579200575099)
            ·
              refine ⟨10145950111226368800862649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763966740817579200575099 10145950111226368800862649)
              ·
                refine ⟨7609462583419776600646987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10145950111226368800862649 7609462583419776600646987)
                ·
                  refine ⟨11414193875129664900970481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7609462583419776600646987 11414193875129664900970481)
                  ·
                    refine ⟨8560645406347248675727861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11414193875129664900970481 8560645406347248675727861)
                    ·
                      refine ⟨802560506845054563349487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8560645406347248675727861 802560506845054563349487)
                      ·
                        rfl

theorem cell23_1562981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1562981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562981 prefixEnd_1562981 := by exact prefixLift 1562981
  have htrace : WordTrace (prefixWord ++ tailWord_1562981) baseStart_1562981 baseEnd_1562981 := by
    simpa [prefixWord, tailWord_1562981, baseEnd_1562981] using wordTrace_append hprefix tailTrace_1562981
  have hstable : (prefixWord ++ tailWord_1562981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562981).length < 2 ^ (prefixWord ++ tailWord_1562981).sum := by decide
  have hdescent : baseEnd_1562981 < baseStart_1562981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562991 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_1562991 : Nat := 118140960795 + 1562991 * 2 ^ 59
def prefixEnd_1562991 : Nat := 4983230072969 + 3 ^ 40 * 1562991 * 2
def baseEnd_1562991 : Nat := 802565641651599524224441

theorem tailTrace_1562991 : CollatzResearch.WordTrace tailWord_1562991 prefixEnd_1562991 802565641651599524224441 := by
  unfold tailWord_1562991
  simp only [CollatzResearch.WordTrace]
  refine ⟨57006965080558019455920827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38004643387038679637280551 57006965080558019455920827)
  ·
    refine ⟨85510447620837029183881241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57006965080558019455920827 85510447620837029183881241)
    ·
      refine ⟨64132835715627771887910931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85510447620837029183881241 64132835715627771887910931)
      ·
        refine ⟨96199253573441657831866397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64132835715627771887910931 96199253573441657831866397)
        ·
          refine ⟨36074720090040621686949899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96199253573441657831866397 36074720090040621686949899)
          ·
            refine ⟨54112080135060932530424849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36074720090040621686949899 54112080135060932530424849)
            ·
              refine ⟨40584060101295699397818637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54112080135060932530424849 40584060101295699397818637)
              ·
                refine ⟨15219022537985887274181989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40584060101295699397818637 15219022537985887274181989)
                ·
                  refine ⟨2853566725872353863909123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15219022537985887274181989 2853566725872353863909123)
                  ·
                    refine ⟨4280350088808530795863685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2853566725872353863909123 4280350088808530795863685)
                    ·
                      refine ⟨802565641651599524224441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4280350088808530795863685 802565641651599524224441)
                      ·
                        rfl

theorem cell23_1562991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_1562991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1562991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1562991 prefixEnd_1562991 := by exact prefixLift 1562991
  have htrace : WordTrace (prefixWord ++ tailWord_1562991) baseStart_1562991 baseEnd_1562991 := by
    simpa [prefixWord, tailWord_1562991, baseEnd_1562991] using wordTrace_append hprefix tailTrace_1562991
  have hstable : (prefixWord ++ tailWord_1562991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562991).length < 2 ^ (prefixWord ++ tailWord_1562991).sum := by decide
  have hdescent : baseEnd_1562991 < baseStart_1562991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563065 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 6]
def baseStart_1563065 : Nat := 118140960795 + 1563065 * 2 ^ 59
def prefixEnd_1563065 : Nat := 4983230072969 + 3 ^ 40 * 1563065 * 2
def baseEnd_1563065 : Nat := 89178182135559137188789

theorem tailTrace_1563065 : CollatzResearch.WordTrace tailWord_1563065 prefixEnd_1563065 89178182135559137188789 := by
  unfold tailWord_1563065
  simp only [CollatzResearch.WordTrace]
  refine ⟨57009664082289930094114649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38006442721526620062743099 57009664082289930094114649)
  ·
    refine ⟨42757248061717447570585987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57009664082289930094114649 42757248061717447570585987)
    ·
      refine ⟨64135872092576171355878981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42757248061717447570585987 64135872092576171355878981)
      ·
        refine ⟨12025476017358032129227309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64135872092576171355878981 12025476017358032129227309)
        ·
          refine ⟨4509553506509262048460241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12025476017358032129227309 4509553506509262048460241)
          ·
            refine ⟨3382165129881946536345181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4509553506509262048460241 3382165129881946536345181)
            ·
              refine ⟨1268311923705729951129443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3382165129881946536345181 1268311923705729951129443)
              ·
                refine ⟨1902467885558594926694165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268311923705729951129443 1902467885558594926694165)
                ·
                  refine ⟨89178182135559137188789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1902467885558594926694165 89178182135559137188789)
                  ·
                    rfl

theorem cell23_1563065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 6].length) (baseStart_1563065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563065 prefixEnd_1563065 := by exact prefixLift 1563065
  have htrace : WordTrace (prefixWord ++ tailWord_1563065) baseStart_1563065 baseEnd_1563065 := by
    simpa [prefixWord, tailWord_1563065, baseEnd_1563065] using wordTrace_append hprefix tailTrace_1563065
  have hstable : (prefixWord ++ tailWord_1563065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563065).length < 2 ^ (prefixWord ++ tailWord_1563065).sum := by decide
  have hdescent : baseEnd_1563065 < baseStart_1563065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563109 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1563109 : Nat := 118140960795 + 1563109 * 2 ^ 59
def prefixEnd_1563109 : Nat := 4983230072969 + 3 ^ 40 * 1563109 * 2
def baseEnd_1563109 : Nat := 802626232368830062548899

theorem tailTrace_1563109 : CollatzResearch.WordTrace tailWord_1563109 prefixEnd_1563109 802626232368830062548899 := by
  unfold tailWord_1563109
  simp only [CollatzResearch.WordTrace]
  refine ⟨57011268894130525608716381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38007512596087017072477587 57011268894130525608716381)
  ·
    refine ⟨21379225835298947103268643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57011268894130525608716381 21379225835298947103268643)
    ·
      refine ⟨32068838752948420654902965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21379225835298947103268643 32068838752948420654902965)
      ·
        refine ⟨3006453633088914436397153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32068838752948420654902965 3006453633088914436397153)
        ·
          refine ⟨2254840224816685827297865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3006453633088914436397153 2254840224816685827297865)
          ·
            refine ⟨1691130168612514370473399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254840224816685827297865 1691130168612514370473399)
            ·
              refine ⟨2536695252918771555710099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691130168612514370473399 2536695252918771555710099)
              ·
                refine ⟨3805042879378157333565149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536695252918771555710099 3805042879378157333565149)
                ·
                  refine ⟨1426891079766809000086931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3805042879378157333565149 1426891079766809000086931)
                  ·
                    refine ⟨2140336619650213500130397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1426891079766809000086931 2140336619650213500130397)
                    ·
                      refine ⟨802626232368830062548899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2140336619650213500130397 802626232368830062548899)
                      ·
                        rfl

theorem cell23_1563109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1563109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563109 prefixEnd_1563109 := by exact prefixLift 1563109
  have htrace : WordTrace (prefixWord ++ tailWord_1563109) baseStart_1563109 baseEnd_1563109 := by
    simpa [prefixWord, tailWord_1563109, baseEnd_1563109] using wordTrace_append hprefix tailTrace_1563109
  have hstable : (prefixWord ++ tailWord_1563109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563109).length < 2 ^ (prefixWord ++ tailWord_1563109).sum := by decide
  have hdescent : baseEnd_1563109 < baseStart_1563109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563128 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1563128 : Nat := 118140960795 + 1563128 * 2 ^ 59
def prefixEnd_1563128 : Nat := 4983230072969 + 3 ^ 40 * 1563128 * 2
def baseEnd_1563128 : Nat := 802635988501265488211311

theorem tailTrace_1563128 : CollatzResearch.WordTrace tailWord_1563128 prefixEnd_1563128 802635988501265488211311 := by
  unfold tailWord_1563128
  simp only [CollatzResearch.WordTrace]
  refine ⟨28505980940530845926829019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38007974587374461235772025 28505980940530845926829019)
  ·
    refine ⟨42758971410796268890243529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28505980940530845926829019 42758971410796268890243529)
    ·
      refine ⟨32069228558097201667682647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42758971410796268890243529 32069228558097201667682647)
      ·
        refine ⟨48103842837145802501523971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32069228558097201667682647 48103842837145802501523971)
        ·
          refine ⟨72155764255718703752285957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48103842837145802501523971 72155764255718703752285957)
          ·
            refine ⟨13529205797947256953553617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72155764255718703752285957 13529205797947256953553617)
            ·
              refine ⟨10146904348460442715165213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13529205797947256953553617 10146904348460442715165213)
              ·
                refine ⟨3805089130672666018186955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10146904348460442715165213 3805089130672666018186955)
                ·
                  refine ⟨5707633696008999027280433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805089130672666018186955 5707633696008999027280433)
                  ·
                    refine ⟨4280725272006749270460325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5707633696008999027280433 4280725272006749270460325)
                    ·
                      refine ⟨802635988501265488211311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4280725272006749270460325 802635988501265488211311)
                      ·
                        rfl

theorem cell23_1563128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1563128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563128 prefixEnd_1563128 := by exact prefixLift 1563128
  have htrace : WordTrace (prefixWord ++ tailWord_1563128) baseStart_1563128 baseEnd_1563128 := by
    simpa [prefixWord, tailWord_1563128, baseEnd_1563128] using wordTrace_append hprefix tailTrace_1563128
  have hstable : (prefixWord ++ tailWord_1563128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563128).length < 2 ^ (prefixWord ++ tailWord_1563128).sum := by decide
  have hdescent : baseEnd_1563128 < baseStart_1563128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563151 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 9]
def baseStart_1563151 : Nat := 118140960795 + 1563151 * 2 ^ 59
def prefixEnd_1563151 : Nat := 4983230072969 + 3 ^ 40 * 1563151 * 2
def baseEnd_1563151 : Nat := 267549266185439632741235

theorem tailTrace_1563151 : CollatzResearch.WordTrace tailWord_1563151 prefixEnd_1563151 267549266185439632741235 := by
  unfold tailWord_1563151
  simp only [CollatzResearch.WordTrace]
  refine ⟨57012800759978366781745307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38008533839985577854496871 57012800759978366781745307)
  ·
    refine ⟨85519201139967550172617961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57012800759978366781745307 85519201139967550172617961)
    ·
      refine ⟨64139400854975662629463471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85519201139967550172617961 64139400854975662629463471)
      ·
        refine ⟨96209101282463493944195207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64139400854975662629463471 96209101282463493944195207)
        ·
          refine ⟨144313651923695240916292811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96209101282463493944195207 144313651923695240916292811)
          ·
            refine ⟨216470477885542861374439217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144313651923695240916292811 216470477885542861374439217)
            ·
              refine ⟨162352858414157146030829413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216470477885542861374439217 162352858414157146030829413)
              ·
                refine ⟨30441160952654464880780515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162352858414157146030829413 30441160952654464880780515)
                ·
                  refine ⟨45661741428981697321170773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30441160952654464880780515 45661741428981697321170773)
                  ·
                    refine ⟨267549266185439632741235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 45661741428981697321170773 267549266185439632741235)
                    ·
                      rfl

theorem cell23_1563151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_1563151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563151 prefixEnd_1563151 := by exact prefixLift 1563151
  have htrace : WordTrace (prefixWord ++ tailWord_1563151) baseStart_1563151 baseEnd_1563151 := by
    simpa [prefixWord, tailWord_1563151, baseEnd_1563151] using wordTrace_append hprefix tailTrace_1563151
  have hstable : (prefixWord ++ tailWord_1563151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563151).length < 2 ^ (prefixWord ++ tailWord_1563151).sum := by decide
  have hdescent : baseEnd_1563151 < baseStart_1563151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563159 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 2, 4]
def baseStart_1563159 : Nat := 118140960795 + 1563159 * 2 ^ 59
def prefixEnd_1563159 : Nat := 4983230072969 + 3 ^ 40 * 1563159 * 2
def baseEnd_1563159 : Nat := 267550635467184955641223

theorem tailTrace_1563159 : CollatzResearch.WordTrace tailWord_1563159 prefixEnd_1563159 267550635467184955641223 := by
  unfold tailWord_1563159
  simp only [CollatzResearch.WordTrace]
  refine ⟨57013092543949384148036531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38008728362632922765357687 57013092543949384148036531)
  ·
    refine ⟨85519638815924076222054797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57013092543949384148036531 85519638815924076222054797)
    ·
      refine ⟨32069864555971528583270549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85519638815924076222054797 32069864555971528583270549)
      ·
        refine ⟨1503274901061165402340807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32069864555971528583270549 1503274901061165402340807)
        ·
          refine ⟨2254912351591748103511211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503274901061165402340807 2254912351591748103511211)
          ·
            refine ⟨3382368527387622155266817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254912351591748103511211 3382368527387622155266817)
            ·
              refine ⟨2536776395540716616450113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3382368527387622155266817 2536776395540716616450113)
              ·
                refine ⟨1902582296655537462337585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2536776395540716616450113 1902582296655537462337585)
                ·
                  refine ⟨1426936722491653096753189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1902582296655537462337585 1426936722491653096753189)
                  ·
                    refine ⟨267550635467184955641223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426936722491653096753189 267550635467184955641223)
                    ·
                      rfl

theorem cell23_1563159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_1563159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563159 prefixEnd_1563159 := by exact prefixLift 1563159
  have htrace : WordTrace (prefixWord ++ tailWord_1563159) baseStart_1563159 baseEnd_1563159 := by
    simpa [prefixWord, tailWord_1563159, baseEnd_1563159] using wordTrace_append hprefix tailTrace_1563159
  have hstable : (prefixWord ++ tailWord_1563159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563159).length < 2 ^ (prefixWord ++ tailWord_1563159).sum := by decide
  have hdescent : baseEnd_1563159 < baseStart_1563159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563172 : List Nat := [2, 3, 1, 5, 1, 2, 1, 8]
def baseStart_1563172 : Nat := 118140960795 + 1563172 * 2 ^ 59
def prefixEnd_1563172 : Nat := 4983230072969 + 3 ^ 40 * 1563172 * 2
def baseEnd_1563172 : Nat := 29728095616669011705967

theorem tailTrace_1563172 : CollatzResearch.WordTrace tailWord_1563172 prefixEnd_1563172 29728095616669011705967 := by
  unfold tailWord_1563172
  simp only [CollatzResearch.WordTrace]
  refine ⟨28506783346451143684129885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38009044461934858245506513 28506783346451143684129885)
  ·
    refine ⟨10690043754919178881548707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28506783346451143684129885 10690043754919178881548707)
    ·
      refine ⟨16035065632378768322323061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10690043754919178881548707 16035065632378768322323061)
      ·
        refine ⟨1503287403035509530217787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16035065632378768322323061 1503287403035509530217787)
        ·
          refine ⟨2254931104553264295326681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503287403035509530217787 2254931104553264295326681)
          ·
            refine ⟨1691198328414948221495011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254931104553264295326681 1691198328414948221495011)
            ·
              refine ⟨2536797492622422332242517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691198328414948221495011 2536797492622422332242517)
              ·
                refine ⟨29728095616669011705967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2536797492622422332242517 29728095616669011705967)
                ·
                  rfl

theorem cell23_1563172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 8].length) (baseStart_1563172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563172 prefixEnd_1563172 := by exact prefixLift 1563172
  have htrace : WordTrace (prefixWord ++ tailWord_1563172) baseStart_1563172 baseEnd_1563172 := by
    simpa [prefixWord, tailWord_1563172, baseEnd_1563172] using wordTrace_append hprefix tailTrace_1563172
  have hstable : (prefixWord ++ tailWord_1563172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563172).length < 2 ^ (prefixWord ++ tailWord_1563172).sum := by decide
  have hdescent : baseEnd_1563172 < baseStart_1563172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563192 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 1, 3, 2]
def baseStart_1563192 : Nat := 118140960795 + 1563192 * 2 ^ 59
def prefixEnd_1563192 : Nat := 4983230072969 + 3 ^ 40 * 1563192 * 2
def baseEnd_1563192 : Nat := 802668851263153237811017

theorem tailTrace_1563192 : CollatzResearch.WordTrace tailWord_1563192 prefixEnd_1563192 802668851263153237811017 := by
  unfold tailWord_1563192
  simp only [CollatzResearch.WordTrace]
  refine ⟨28507148076414915391993915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38009530768553220522658553 28507148076414915391993915)
  ·
    refine ⟨42760722114622373087990873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28507148076414915391993915 42760722114622373087990873)
    ·
      refine ⟨32070541585966779815993155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42760722114622373087990873 32070541585966779815993155)
      ·
        refine ⟨48105812378950169723989733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32070541585966779815993155 48105812378950169723989733)
        ·
          refine ⟨9019839821053156823248075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48105812378950169723989733 9019839821053156823248075)
          ·
            refine ⟨13529759731579735234872113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9019839821053156823248075 13529759731579735234872113)
            ·
              refine ⟨10147319798684801426154085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13529759731579735234872113 10147319798684801426154085)
              ·
                refine ⟨1902622462253400267403891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10147319798684801426154085 1902622462253400267403891)
                ·
                  refine ⟨2853933693380100401105837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1902622462253400267403891 2853933693380100401105837)
                  ·
                    refine ⟨1070225135017537650414689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2853933693380100401105837 1070225135017537650414689)
                    ·
                      refine ⟨802668851263153237811017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070225135017537650414689 802668851263153237811017)
                      ·
                        rfl

theorem cell23_1563192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_1563192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563192 prefixEnd_1563192 := by exact prefixLift 1563192
  have htrace : WordTrace (prefixWord ++ tailWord_1563192) baseStart_1563192 baseEnd_1563192 := by
    simpa [prefixWord, tailWord_1563192, baseEnd_1563192] using wordTrace_append hprefix tailTrace_1563192
  have hstable : (prefixWord ++ tailWord_1563192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563192).length < 2 ^ (prefixWord ++ tailWord_1563192).sum := by decide
  have hdescent : baseEnd_1563192 < baseStart_1563192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563208 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1563208 : Nat := 118140960795 + 1563208 * 2 ^ 59
def prefixEnd_1563208 : Nat := 4983230072969 + 3 ^ 40 * 1563208 * 2
def baseEnd_1563208 : Nat := 802677066953625175210943

theorem tailTrace_1563208 : CollatzResearch.WordTrace tailWord_1563208 prefixEnd_1563208 802677066953625175210943 := by
  unfold tailWord_1563208
  simp only [CollatzResearch.WordTrace]
  refine ⟨28507439860385932758285139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38009919813847910344380185 28507439860385932758285139)
  ·
    refine ⟨42761159790578899137427709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28507439860385932758285139 42761159790578899137427709)
    ·
      refine ⟨16035434921467087176535391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42761159790578899137427709 16035434921467087176535391)
      ·
        refine ⟨24053152382200630764803087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16035434921467087176535391 24053152382200630764803087)
        ·
          refine ⟨36079728573300946147204631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24053152382200630764803087 36079728573300946147204631)
          ·
            refine ⟨54119592859951419220806947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36079728573300946147204631 54119592859951419220806947)
            ·
              refine ⟨81179389289927128831210421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54119592859951419220806947 81179389289927128831210421)
              ·
                refine ⟨7610567745930668327925977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81179389289927128831210421 7610567745930668327925977)
                ·
                  refine ⟨5707925809448001245944483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7610567745930668327925977 5707925809448001245944483)
                  ·
                    refine ⟨8561888714172001868916725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5707925809448001245944483 8561888714172001868916725)
                    ·
                      refine ⟨802677066953625175210943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8561888714172001868916725 802677066953625175210943)
                      ·
                        rfl

theorem cell23_1563208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1563208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563208 prefixEnd_1563208 := by exact prefixLift 1563208
  have htrace : WordTrace (prefixWord ++ tailWord_1563208) baseStart_1563208 baseEnd_1563208 := by
    simpa [prefixWord, tailWord_1563208, baseEnd_1563208] using wordTrace_append hprefix tailTrace_1563208
  have hstable : (prefixWord ++ tailWord_1563208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563208).length < 2 ^ (prefixWord ++ tailWord_1563208).sum := by decide
  have hdescent : baseEnd_1563208 < baseStart_1563208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563245 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1563245 : Nat := 118140960795 + 1563245 * 2 ^ 59
def prefixEnd_1563245 : Nat := 4983230072969 + 3 ^ 40 * 1563245 * 2
def baseEnd_1563245 : Nat := 89188451748649058938697

theorem tailTrace_1563245 : CollatzResearch.WordTrace tailWord_1563245 prefixEnd_1563245 89188451748649058938697 := by
  unfold tailWord_1563245
  simp only [CollatzResearch.WordTrace]
  refine ⟨57016229221637820835667189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38010819481091880557111459 57016229221637820835667189)
  ·
    refine ⟨5345271489528545703343799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57016229221637820835667189 5345271489528545703343799)
    ·
      refine ⟨8017907234292818555015699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345271489528545703343799 8017907234292818555015699)
      ·
        refine ⟨12026860851439227832523549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8017907234292818555015699 12026860851439227832523549)
        ·
          refine ⟨4510072819289710437196331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12026860851439227832523549 4510072819289710437196331)
          ·
            refine ⟨6765109228934565655794497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510072819289710437196331 6765109228934565655794497)
            ·
              refine ⟨5073831921700924241845873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6765109228934565655794497 5073831921700924241845873)
              ·
                refine ⟨3805373941275693181384405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073831921700924241845873 3805373941275693181384405)
                ·
                  refine ⟨89188451748649058938697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3805373941275693181384405 89188451748649058938697)
                  ·
                    rfl

theorem cell23_1563245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1563245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563245 prefixEnd_1563245 := by exact prefixLift 1563245
  have htrace : WordTrace (prefixWord ++ tailWord_1563245) baseStart_1563245 baseEnd_1563245 := by
    simpa [prefixWord, tailWord_1563245, baseEnd_1563245] using wordTrace_append hprefix tailTrace_1563245
  have hstable : (prefixWord ++ tailWord_1563245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563245).length < 2 ^ (prefixWord ++ tailWord_1563245).sum := by decide
  have hdescent : baseEnd_1563245 < baseStart_1563245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563290 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1563290 : Nat := 118140960795 + 1563290 * 2 ^ 59
def prefixEnd_1563290 : Nat := 4983230072969 + 3 ^ 40 * 1563290 * 2
def baseEnd_1563290 : Nat := 802719172367293854385567

theorem tailTrace_1563290 : CollatzResearch.WordTrace tailWord_1563290 prefixEnd_1563290 802719172367293854385567 := by
  unfold tailWord_1563290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14254467626618698380263831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38011913670983195680703549 14254467626618698380263831)
  ·
    refine ⟨21381701439928047570395747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14254467626618698380263831 21381701439928047570395747)
    ·
      refine ⟨32072552159892071355593621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21381701439928047570395747 32072552159892071355593621)
      ·
        refine ⟨1503400882494940844793451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32072552159892071355593621 1503400882494940844793451)
        ·
          refine ⟨2255101323742411267190177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503400882494940844793451 2255101323742411267190177)
          ·
            refine ⟨1691325992806808450392633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255101323742411267190177 1691325992806808450392633)
            ·
              refine ⟨1268494494605106337794475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691325992806808450392633 1268494494605106337794475)
              ·
                refine ⟨1902741741907659506691713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268494494605106337794475 1902741741907659506691713)
                ·
                  refine ⟨1427056306430744630018785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1902741741907659506691713 1427056306430744630018785)
                  ·
                    refine ⟨1070292229823058472514089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1427056306430744630018785 1070292229823058472514089)
                    ·
                      refine ⟨802719172367293854385567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070292229823058472514089 802719172367293854385567)
                      ·
                        rfl

theorem cell23_1563290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1563290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563290 prefixEnd_1563290 := by exact prefixLift 1563290
  have htrace : WordTrace (prefixWord ++ tailWord_1563290) baseStart_1563290 baseEnd_1563290 := by
    simpa [prefixWord, tailWord_1563290, baseEnd_1563290] using wordTrace_append hprefix tailTrace_1563290
  have hstable : (prefixWord ++ tailWord_1563290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563290).length < 2 ^ (prefixWord ++ tailWord_1563290).sum := by decide
  have hdescent : baseEnd_1563290 < baseStart_1563290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563396 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1563396 : Nat := 118140960795 + 1563396 * 2 ^ 59
def prefixEnd_1563396 : Nat := 4983230072969 + 3 ^ 40 * 1563396 * 2
def baseEnd_1563396 : Nat := 802773601316670439660079

theorem tailTrace_1563396 : CollatzResearch.WordTrace tailWord_1563396 prefixEnd_1563396 802773601316670439660079 := by
  unfold tailWord_1563396
  simp only [CollatzResearch.WordTrace]
  refine ⟨28510868322045386812207021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38014491096060515749609361 28510868322045386812207021)
  ·
    refine ⟨10691575620767020054577633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28510868322045386812207021 10691575620767020054577633)
    ·
      refine ⟨8018681715575265040933225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10691575620767020054577633 8018681715575265040933225)
      ·
        refine ⟨6014011286681448780699919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8018681715575265040933225 6014011286681448780699919)
        ·
          refine ⟨9021016930022173171049879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6014011286681448780699919 9021016930022173171049879)
          ·
            refine ⟨13531525395033259756574819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9021016930022173171049879 13531525395033259756574819)
            ·
              refine ⟨20297288092549889634862229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13531525395033259756574819 20297288092549889634862229)
              ·
                refine ⟨951435379338276076634167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20297288092549889634862229 951435379338276076634167)
                ·
                  refine ⟨1427153069007414114951251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951435379338276076634167 1427153069007414114951251)
                  ·
                    refine ⟨2140729603511121172426877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1427153069007414114951251 2140729603511121172426877)
                    ·
                      refine ⟨802773601316670439660079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2140729603511121172426877 802773601316670439660079)
                      ·
                        rfl

theorem cell23_1563396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1563396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563396 prefixEnd_1563396 := by exact prefixLift 1563396
  have htrace : WordTrace (prefixWord ++ tailWord_1563396) baseStart_1563396 baseEnd_1563396 := by
    simpa [prefixWord, tailWord_1563396, baseEnd_1563396] using wordTrace_append hprefix tailTrace_1563396
  have hstable : (prefixWord ++ tailWord_1563396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563396).length < 2 ^ (prefixWord ++ tailWord_1563396).sum := by decide
  have hdescent : baseEnd_1563396 < baseStart_1563396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563425 : List Nat := [1, 2, 3, 2, 1, 2, 3, 9]
def baseStart_1563425 : Nat := 118140960795 + 1563425 * 2 ^ 59
def prefixEnd_1563425 : Nat := 4983230072969 + 3 ^ 40 * 1563425 * 2
def baseEnd_1563425 : Nat := 29732907120579660229535

theorem tailTrace_1563425 : CollatzResearch.WordTrace tailWord_1563425 prefixEnd_1563425 29732907120579660229535 := by
  unfold tailWord_1563425
  simp only [CollatzResearch.WordTrace]
  refine ⟨57022794360985711577219729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38015196240657141051479819 57022794360985711577219729)
  ·
    refine ⟨42767095770739283682914797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57022794360985711577219729 42767095770739283682914797)
    ·
      refine ⟨16037660914027231381093049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42767095770739283682914797 16037660914027231381093049)
      ·
        refine ⟨12028245685520423535819787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16037660914027231381093049 12028245685520423535819787)
        ·
          refine ⟨18042368528280635303729681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028245685520423535819787 18042368528280635303729681)
          ·
            refine ⟨13531776396210476477797261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18042368528280635303729681 13531776396210476477797261)
            ·
              refine ⟨5074416148578928679173973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13531776396210476477797261 5074416148578928679173973)
              ·
                refine ⟨29732907120579660229535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5074416148578928679173973 29732907120579660229535)
                ·
                  rfl

theorem cell23_1563425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 9].length) (baseStart_1563425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563425 prefixEnd_1563425 := by exact prefixLift 1563425
  have htrace : WordTrace (prefixWord ++ tailWord_1563425) baseStart_1563425 baseEnd_1563425 := by
    simpa [prefixWord, tailWord_1563425, baseEnd_1563425] using wordTrace_append hprefix tailTrace_1563425
  have hstable : (prefixWord ++ tailWord_1563425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563425).length < 2 ^ (prefixWord ++ tailWord_1563425).sum := by decide
  have hdescent : baseEnd_1563425 < baseStart_1563425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563432 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1563432 : Nat := 118140960795 + 1563432 * 2 ^ 59
def prefixEnd_1563432 : Nat := 4983230072969 + 3 ^ 40 * 1563432 * 2
def baseEnd_1563432 : Nat := 802792086620232298809913

theorem tailTrace_1563432 : CollatzResearch.WordTrace tailWord_1563432 prefixEnd_1563432 802792086620232298809913 := by
  unfold tailWord_1563432
  simp only [CollatzResearch.WordTrace]
  refine ⟨28511524835980175886362275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38015366447973567848483033 28511524835980175886362275)
  ·
    refine ⟨42767287253970263829543413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28511524835980175886362275 42767287253970263829543413)
    ·
      refine ⟨4009433180059712234019695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42767287253970263829543413 4009433180059712234019695)
      ·
        refine ⟨6014149770089568351029543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009433180059712234019695 6014149770089568351029543)
        ·
          refine ⟨9021224655134352526544315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6014149770089568351029543 9021224655134352526544315)
          ·
            refine ⟨13531836982701528789816473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9021224655134352526544315 13531836982701528789816473)
            ·
              refine ⟨10148877737026146592362355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13531836982701528789816473 10148877737026146592362355)
              ·
                refine ⟨15223316605539219888543533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10148877737026146592362355 15223316605539219888543533)
                ·
                  refine ⟨5708743727077207458203825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15223316605539219888543533 5708743727077207458203825)
                  ·
                    refine ⟨4281557795307905593652869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5708743727077207458203825 4281557795307905593652869)
                    ·
                      refine ⟨802792086620232298809913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4281557795307905593652869 802792086620232298809913)
                      ·
                        rfl

theorem cell23_1563432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1563432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563432 prefixEnd_1563432 := by exact prefixLift 1563432
  have htrace : WordTrace (prefixWord ++ tailWord_1563432) baseStart_1563432 baseEnd_1563432 := by
    simpa [prefixWord, tailWord_1563432, baseEnd_1563432] using wordTrace_append hprefix tailTrace_1563432
  have hstable : (prefixWord ++ tailWord_1563432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563432).length < 2 ^ (prefixWord ++ tailWord_1563432).sum := by decide
  have hdescent : baseEnd_1563432 < baseStart_1563432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563473 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 1, 2, 3]
def baseStart_1563473 : Nat := 118140960795 + 1563473 * 2 ^ 59
def prefixEnd_1563473 : Nat := 4983230072969 + 3 ^ 40 * 1563473 * 2
def baseEnd_1563473 : Nat := 802813139327066638397225

theorem tailTrace_1563473 : CollatzResearch.WordTrace tailWord_1563473 prefixEnd_1563473 802813139327066638397225 := by
  unfold tailWord_1563473
  simp only [CollatzResearch.WordTrace]
  refine ⟨57024545064811815774967073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38016363376541210516644715 57024545064811815774967073)
  ·
    refine ⟨42768408798608861831225305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57024545064811815774967073 42768408798608861831225305)
    ·
      refine ⟨32076306598956646373418979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42768408798608861831225305 32076306598956646373418979)
      ·
        refine ⟨48114459898434969560128469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32076306598956646373418979 48114459898434969560128469)
        ·
          refine ⟨1127682653869569599065511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48114459898434969560128469 1127682653869569599065511)
          ·
            refine ⟨1691523980804354398598267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127682653869569599065511 1691523980804354398598267)
            ·
              refine ⟨2537285971206531597897401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691523980804354398598267 2537285971206531597897401)
              ·
                refine ⟨1902964478404898698423051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537285971206531597897401 1902964478404898698423051)
                ·
                  refine ⟨2854446717607348047634577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1902964478404898698423051 2854446717607348047634577)
                  ·
                    refine ⟨2140835038205511035725933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2854446717607348047634577 2140835038205511035725933)
                    ·
                      refine ⟨802813139327066638397225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2140835038205511035725933 802813139327066638397225)
                      ·
                        rfl

theorem cell23_1563473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_1563473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563473 prefixEnd_1563473 := by exact prefixLift 1563473
  have htrace : WordTrace (prefixWord ++ tailWord_1563473) baseStart_1563473 baseEnd_1563473 := by
    simpa [prefixWord, tailWord_1563473, baseEnd_1563473] using wordTrace_append hprefix tailTrace_1563473
  have hstable : (prefixWord ++ tailWord_1563473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563473).length < 2 ^ (prefixWord ++ tailWord_1563473).sum := by decide
  have hdescent : baseEnd_1563473 < baseStart_1563473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563626 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1563626 : Nat := 118140960795 + 1563626 * 2 ^ 59
def prefixEnd_1563626 : Nat := 4983230072969 + 3 ^ 40 * 1563626 * 2
def baseEnd_1563626 : Nat := 267630567289068179928007

theorem tailTrace_1563626 : CollatzResearch.WordTrace tailWord_1563626 prefixEnd_1563626 267630567289068179928007 := by
  unfold tailWord_1563626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257531358314380726321683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38020083622171681936857821 14257531358314380726321683)
  ·
    refine ⟨21386297037471571089482525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14257531358314380726321683 21386297037471571089482525)
    ·
      refine ⟨8019861389051839158555947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21386297037471571089482525 8019861389051839158555947)
      ·
        refine ⟨12029792083577758737833921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8019861389051839158555947 12029792083577758737833921)
        ·
          refine ⟨9022344062683319053375441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12029792083577758737833921 9022344062683319053375441)
          ·
            refine ⟨6766758047012489290031581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9022344062683319053375441 6766758047012489290031581)
            ·
              refine ⟨2537534267629683483761843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6766758047012489290031581 2537534267629683483761843)
              ·
                refine ⟨3806301401444525225642765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537534267629683483761843 3806301401444525225642765)
                ·
                  refine ⟨1427363025541696959616037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3806301401444525225642765 1427363025541696959616037)
                  ·
                    refine ⟨267630567289068179928007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427363025541696959616037 267630567289068179928007)
                    ·
                      rfl

theorem cell23_1563626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1563626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563626 prefixEnd_1563626 := by exact prefixLift 1563626
  have htrace : WordTrace (prefixWord ++ tailWord_1563626) baseStart_1563626 baseEnd_1563626 := by
    simpa [prefixWord, tailWord_1563626, baseEnd_1563626] using wordTrace_append hprefix tailTrace_1563626
  have hstable : (prefixWord ++ tailWord_1563626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563626).length < 2 ^ (prefixWord ++ tailWord_1563626).sum := by decide
  have hdescent : baseEnd_1563626 < baseStart_1563626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563642 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1563642 : Nat := 118140960795 + 1563642 * 2 ^ 59
def prefixEnd_1563642 : Nat := 4983230072969 + 3 ^ 40 * 1563642 * 2
def baseEnd_1563642 : Nat := 802899917557676477183947

theorem tailTrace_1563642 : CollatzResearch.WordTrace tailWord_1563642 prefixEnd_1563642 802899917557676477183947 := by
  unfold tailWord_1563642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257677250299889409467295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38020472667466371758579453 14257677250299889409467295)
  ·
    refine ⟨21386515875449834114200943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14257677250299889409467295 21386515875449834114200943)
    ·
      refine ⟨32079773813174751171301415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21386515875449834114200943 32079773813174751171301415)
      ·
        refine ⟨48119660719762126756952123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32079773813174751171301415 48119660719762126756952123)
        ·
          refine ⟨72179491079643190135428185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48119660719762126756952123 72179491079643190135428185)
          ·
            refine ⟨54134618309732392601571139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72179491079643190135428185 54134618309732392601571139)
            ·
              refine ⟨81201927464598588902356709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54134618309732392601571139 81201927464598588902356709)
              ·
                refine ⟨15225361399612235419191883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81201927464598588902356709 15225361399612235419191883)
                ·
                  refine ⟨22838042099418353128787825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15225361399612235419191883 22838042099418353128787825)
                  ·
                    refine ⟨17128531574563764846590869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22838042099418353128787825 17128531574563764846590869)
                    ·
                      refine ⟨802899917557676477183947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17128531574563764846590869 802899917557676477183947)
                      ·
                        rfl

theorem cell23_1563642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1563642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563642 prefixEnd_1563642 := by exact prefixLift 1563642
  have htrace : WordTrace (prefixWord ++ tailWord_1563642) baseStart_1563642 baseEnd_1563642 := by
    simpa [prefixWord, tailWord_1563642, baseEnd_1563642] using wordTrace_append hprefix tailTrace_1563642
  have hstable : (prefixWord ++ tailWord_1563642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563642).length < 2 ^ (prefixWord ++ tailWord_1563642).sum := by decide
  have hdescent : baseEnd_1563642 < baseStart_1563642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563650 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1563650 : Nat := 118140960795 + 1563650 * 2 ^ 59
def prefixEnd_1563650 : Nat := 4983230072969 + 3 ^ 40 * 1563650 * 2
def baseEnd_1563650 : Nat := 802904025402912445883911

theorem tailTrace_1563650 : CollatzResearch.WordTrace tailWord_1563650 prefixEnd_1563650 802904025402912445883911 := by
  unfold tailWord_1563650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257750196292643751040101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38020667190113716669440269 14257750196292643751040101)
  ·
    refine ⟨2673328161804870703320019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14257750196292643751040101 2673328161804870703320019)
    ·
      refine ⟨4009992242707306054980029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673328161804870703320019 4009992242707306054980029)
      ·
        refine ⟨1503747091015239770617511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4009992242707306054980029 1503747091015239770617511)
        ·
          refine ⟨2255620636522859655926267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503747091015239770617511 2255620636522859655926267)
          ·
            refine ⟨3383430954784289483889401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255620636522859655926267 3383430954784289483889401)
            ·
              refine ⟨2537573216088217112917051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383430954784289483889401 2537573216088217112917051)
              ·
                refine ⟨3806359824132325669375577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537573216088217112917051 3806359824132325669375577)
                ·
                  refine ⟨2854769868099244252031683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806359824132325669375577 2854769868099244252031683)
                  ·
                    refine ⟨4282154802148866378047525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2854769868099244252031683 4282154802148866378047525)
                    ·
                      refine ⟨802904025402912445883911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4282154802148866378047525 802904025402912445883911)
                      ·
                        rfl

theorem cell23_1563650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1563650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563650 prefixEnd_1563650 := by exact prefixLift 1563650
  have htrace : WordTrace (prefixWord ++ tailWord_1563650) baseStart_1563650 baseEnd_1563650 := by
    simpa [prefixWord, tailWord_1563650, baseEnd_1563650] using wordTrace_append hprefix tailTrace_1563650
  have hstable : (prefixWord ++ tailWord_1563650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563650).length < 2 ^ (prefixWord ++ tailWord_1563650).sum := by decide
  have hdescent : baseEnd_1563650 < baseStart_1563650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563677 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1563677 : Nat := 118140960795 + 1563677 * 2 ^ 59
def prefixEnd_1563677 : Nat := 4983230072969 + 3 ^ 40 * 1563677 * 2
def baseEnd_1563677 : Nat := 267639296460194613415429

theorem tailTrace_1563677 : CollatzResearch.WordTrace tailWord_1563677 prefixEnd_1563677 267639296460194613415429 := by
  unfold tailWord_1563677
  simp only [CollatzResearch.WordTrace]
  refine ⟨57031985556072758615393285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38021323704048505743595523 57031985556072758615393285)
  ·
    refine ⟨10693497291763642240386241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57031985556072758615393285 10693497291763642240386241)
    ·
      refine ⟨8020122968822731680289681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10693497291763642240386241 8020122968822731680289681)
      ·
        refine ⟨6015092226617048760217261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8020122968822731680289681 6015092226617048760217261)
        ·
          refine ⟨2255659584981393285081473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6015092226617048760217261 2255659584981393285081473)
          ·
            refine ⟨1691744688736044963811105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255659584981393285081473 1691744688736044963811105)
            ·
              refine ⟨1268808516552033722858329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691744688736044963811105 1268808516552033722858329)
              ·
                refine ⟨951606387414025292143747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268808516552033722858329 951606387414025292143747)
                ·
                  refine ⟨1427409581121037938215621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951606387414025292143747 1427409581121037938215621)
                  ·
                    refine ⟨267639296460194613415429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427409581121037938215621 267639296460194613415429)
                    ·
                      rfl

theorem cell23_1563677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1563677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563677 prefixEnd_1563677 := by exact prefixLift 1563677
  have htrace : WordTrace (prefixWord ++ tailWord_1563677) baseStart_1563677 baseEnd_1563677 := by
    simpa [prefixWord, tailWord_1563677, baseEnd_1563677] using wordTrace_append hprefix tailTrace_1563677
  have hstable : (prefixWord ++ tailWord_1563677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563677).length < 2 ^ (prefixWord ++ tailWord_1563677).sum := by decide
  have hdescent : baseEnd_1563677 < baseStart_1563677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563699 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 6, 4]
def baseStart_1563699 : Nat := 118140960795 + 1563699 * 2 ^ 59
def prefixEnd_1563699 : Nat := 4983230072969 + 3 ^ 40 * 1563699 * 2
def baseEnd_1563699 : Nat := 267643061984994251390395

theorem tailTrace_1563699 : CollatzResearch.WordTrace tailWord_1563699 prefixEnd_1563699 267643061984994251390395 := by
  unfold tailWord_1563699
  simp only [CollatzResearch.WordTrace]
  refine ⟨57032787961993056372694151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38021858641328704248462767 57032787961993056372694151)
  ·
    refine ⟨85549181942989584559041227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57032787961993056372694151 85549181942989584559041227)
    ·
      refine ⟨128323772914484376838561841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85549181942989584559041227 128323772914484376838561841)
      ·
        refine ⟨96242829685863282628921381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128323772914484376838561841 96242829685863282628921381)
        ·
          refine ⟨18045530566099365492922759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96242829685863282628921381 18045530566099365492922759)
          ·
            refine ⟨27068295849149048239384139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18045530566099365492922759 27068295849149048239384139)
            ·
              refine ⟨40602443773723572359076209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27068295849149048239384139 40602443773723572359076209)
              ·
                refine ⟨30451832830292679269307157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40602443773723572359076209 30451832830292679269307157)
                ·
                  refine ⟨1427429663919969340748773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30451832830292679269307157 1427429663919969340748773)
                  ·
                    refine ⟨267643061984994251390395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427429663919969340748773 267643061984994251390395)
                    ·
                      rfl

theorem cell23_1563699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 4].length) (baseStart_1563699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563699 prefixEnd_1563699 := by exact prefixLift 1563699
  have htrace : WordTrace (prefixWord ++ tailWord_1563699) baseStart_1563699 baseEnd_1563699 := by
    simpa [prefixWord, tailWord_1563699, baseEnd_1563699] using wordTrace_append hprefix tailTrace_1563699
  have hstable : (prefixWord ++ tailWord_1563699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563699).length < 2 ^ (prefixWord ++ tailWord_1563699).sum := by decide
  have hdescent : baseEnd_1563699 < baseStart_1563699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563700 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1563700 : Nat := 118140960795 + 1563700 * 2 ^ 59
def prefixEnd_1563700 : Nat := 4983230072969 + 3 ^ 40 * 1563700 * 2
def baseEnd_1563700 : Nat := 802929699435637250258681

theorem tailTrace_1563700 : CollatzResearch.WordTrace tailWord_1563700 prefixEnd_1563700 802929699435637250258681 := by
  unfold tailWord_1563700
  simp only [CollatzResearch.WordTrace]
  refine ⟨28516412217494716771740277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38021882956659622362320369 28516412217494716771740277)
  ·
    refine ⟨2673413645390129697350651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28516412217494716771740277 2673413645390129697350651)
    ·
      refine ⟨4010120468085194546025977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673413645390129697350651 4010120468085194546025977)
      ·
        refine ⟨3007590351063895909519483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4010120468085194546025977 3007590351063895909519483)
        ·
          refine ⟨4511385526595843864279225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007590351063895909519483 4511385526595843864279225)
          ·
            refine ⟨3383539144946882898209419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4511385526595843864279225 3383539144946882898209419)
            ·
              refine ⟨5075308717420324347314129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383539144946882898209419 5075308717420324347314129)
              ·
                refine ⟨3806481538065243260485597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5075308717420324347314129 3806481538065243260485597)
                ·
                  refine ⟨1427430576774466222682099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3806481538065243260485597 1427430576774466222682099)
                  ·
                    refine ⟨2141145865161699334023149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1427430576774466222682099 2141145865161699334023149)
                    ·
                      refine ⟨802929699435637250258681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2141145865161699334023149 802929699435637250258681)
                      ·
                        rfl

theorem cell23_1563700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1563700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563700 prefixEnd_1563700 := by exact prefixLift 1563700
  have htrace : WordTrace (prefixWord ++ tailWord_1563700) baseStart_1563700 baseEnd_1563700 := by
    simpa [prefixWord, tailWord_1563700, baseEnd_1563700] using wordTrace_append hprefix tailTrace_1563700
  have hstable : (prefixWord ++ tailWord_1563700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563700).length < 2 ^ (prefixWord ++ tailWord_1563700).sum := by decide
  have hdescent : baseEnd_1563700 < baseStart_1563700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563710 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_1563710 : Nat := 118140960795 + 1563710 * 2 ^ 59
def prefixEnd_1563710 : Nat := 4983230072969 + 3 ^ 40 * 1563710 * 2
def baseEnd_1563710 : Nat := 802934834242182211133635

theorem tailTrace_1563710 : CollatzResearch.WordTrace tailWord_1563710 prefixEnd_1563710 802934834242182211133635 := by
  unfold tailWord_1563710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129148645619150656418073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38022126109968803500896389 7129148645619150656418073)
  ·
    refine ⟨5346861484214362992313555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7129148645619150656418073 5346861484214362992313555)
    ·
      refine ⟨8020292226321544488470333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346861484214362992313555 8020292226321544488470333)
      ·
        refine ⟨3007609584870579183176375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8020292226321544488470333 3007609584870579183176375)
        ·
          refine ⟨4511414377305868774764563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007609584870579183176375 4511414377305868774764563)
          ·
            refine ⟨6767121565958803162146845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4511414377305868774764563 6767121565958803162146845)
            ·
              refine ⟨2537670587234551185805067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6767121565958803162146845 2537670587234551185805067)
              ·
                refine ⟨3806505880851826778707601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537670587234551185805067 3806505880851826778707601)
                ·
                  refine ⟨2854879410638870084030701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806505880851826778707601 2854879410638870084030701)
                  ·
                    refine ⟨1070579778989576281511513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2854879410638870084030701 1070579778989576281511513)
                    ·
                      refine ⟨802934834242182211133635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070579778989576281511513 802934834242182211133635)
                      ·
                        rfl

theorem cell23_1563710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_1563710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563710 prefixEnd_1563710 := by exact prefixLift 1563710
  have htrace : WordTrace (prefixWord ++ tailWord_1563710) baseStart_1563710 baseEnd_1563710 := by
    simpa [prefixWord, tailWord_1563710, baseEnd_1563710] using wordTrace_append hprefix tailTrace_1563710
  have hstable : (prefixWord ++ tailWord_1563710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563710).length < 2 ^ (prefixWord ++ tailWord_1563710).sum := by decide
  have hdescent : baseEnd_1563710 < baseStart_1563710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563740 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_1563740 : Nat := 118140960795 + 1563740 * 2 ^ 59
def prefixEnd_1563740 : Nat := 4983230072969 + 3 ^ 40 * 1563740 * 2
def baseEnd_1563740 : Nat := 802950238661817093758497

theorem tailTrace_1563740 : CollatzResearch.WordTrace tailWord_1563740 prefixEnd_1563740 802950238661817093758497 := by
  unfold tailWord_1563740
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517141677422260187468337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38022855569896346916624449 28517141677422260187468337)
  ·
    refine ⟨21387856258066695140601253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28517141677422260187468337 21387856258066695140601253)
    ·
      refine ⟨4010223048387505338862735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21387856258066695140601253 4010223048387505338862735)
      ·
        refine ⟨6015334572581258008294103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010223048387505338862735 6015334572581258008294103)
        ·
          refine ⟨9023001858871887012441155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015334572581258008294103 9023001858871887012441155)
          ·
            refine ⟨13534502788307830518661733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9023001858871887012441155 13534502788307830518661733)
            ·
              refine ⟨2537719272807718222249075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13534502788307830518661733 2537719272807718222249075)
              ·
                refine ⟨3806578909211577333373613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537719272807718222249075 3806578909211577333373613)
                ·
                  refine ⟨1427467090954341500015105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3806578909211577333373613 1427467090954341500015105)
                  ·
                    refine ⟨1070600318215756125011329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1427467090954341500015105 1070600318215756125011329)
                    ·
                      refine ⟨802950238661817093758497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070600318215756125011329 802950238661817093758497)
                      ·
                        rfl

theorem cell23_1563740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_1563740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563740 prefixEnd_1563740 := by exact prefixLift 1563740
  have htrace : WordTrace (prefixWord ++ tailWord_1563740) baseStart_1563740 baseEnd_1563740 := by
    simpa [prefixWord, tailWord_1563740, baseEnd_1563740] using wordTrace_append hprefix tailTrace_1563740
  have hstable : (prefixWord ++ tailWord_1563740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563740).length < 2 ^ (prefixWord ++ tailWord_1563740).sum := by decide
  have hdescent : baseEnd_1563740 < baseStart_1563740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563860 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1563860 : Nat := 118140960795 + 1563860 * 2 ^ 59
def prefixEnd_1563860 : Nat := 4983230072969 + 3 ^ 40 * 1563860 * 2
def baseEnd_1563860 : Nat := 803011856340356624257945

theorem tailTrace_1563860 : CollatzResearch.WordTrace tailWord_1563860 prefixEnd_1563860 803011856340356624257945 := by
  unfold tailWord_1563860
  simp only [CollatzResearch.WordTrace]
  refine ⟨28519330057204890434652517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38025773409606520579536689 28519330057204890434652517)
  ·
    refine ⟨5347374385725916956497347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28519330057204890434652517 5347374385725916956497347)
    ·
      refine ⟨8021061578588875434746021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5347374385725916956497347 8021061578588875434746021)
      ·
        refine ⟨1503949045985414144014879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8021061578588875434746021 1503949045985414144014879)
        ·
          refine ⟨2255923568978121216022319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503949045985414144014879 2255923568978121216022319)
          ·
            refine ⟨3383885353467181824033479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255923568978121216022319 3383885353467181824033479)
            ·
              refine ⟨5075828030200772736050219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383885353467181824033479 5075828030200772736050219)
              ·
                refine ⟨7613742045301159104075329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075828030200772736050219 7613742045301159104075329)
                ·
                  refine ⟨5710306533975869328056497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613742045301159104075329 5710306533975869328056497)
                  ·
                    refine ⟨4282729900481901996042373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710306533975869328056497 4282729900481901996042373)
                    ·
                      refine ⟨803011856340356624257945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4282729900481901996042373 803011856340356624257945)
                      ·
                        rfl

theorem cell23_1563860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1563860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563860 prefixEnd_1563860 := by exact prefixLift 1563860
  have htrace : WordTrace (prefixWord ++ tailWord_1563860) baseStart_1563860 baseEnd_1563860 := by
    simpa [prefixWord, tailWord_1563860, baseEnd_1563860] using wordTrace_append hprefix tailTrace_1563860
  have hstable : (prefixWord ++ tailWord_1563860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563860).length < 2 ^ (prefixWord ++ tailWord_1563860).sum := by decide
  have hdescent : baseEnd_1563860 < baseStart_1563860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563883 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 2, 5]
def baseStart_1563883 : Nat := 118140960795 + 1563883 * 2 ^ 59
def prefixEnd_1563883 : Nat := 4983230072969 + 3 ^ 40 * 1563883 * 2
def baseEnd_1563883 : Nat := 267674555465136678090113

theorem tailTrace_1563883 : CollatzResearch.WordTrace tailWord_1563883 prefixEnd_1563883 267674555465136678090113 := by
  unfold tailWord_1563883
  simp only [CollatzResearch.WordTrace]
  refine ⟨57039498993326455797392303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38026332662217637198261535 57039498993326455797392303)
  ·
    refine ⟨85559248489989683696088455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57039498993326455797392303 85559248489989683696088455)
    ·
      refine ⟨128338872734984525544132683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85559248489989683696088455 128338872734984525544132683)
      ·
        refine ⟨192508309102476788316199025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128338872734984525544132683 192508309102476788316199025)
        ·
          refine ⟨144381231826857591237149269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192508309102476788316199025 144381231826857591237149269)
          ·
            refine ⟨1691967560470987397310343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 144381231826857591237149269 1691967560470987397310343)
            ·
              refine ⟨2537951340706481095965515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691967560470987397310343 2537951340706481095965515)
              ·
                refine ⟨3806927011059721643948273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537951340706481095965515 3806927011059721643948273)
                ·
                  refine ⟨2855195258294791232961205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806927011059721643948273 2855195258294791232961205)
                  ·
                    refine ⟨267674555465136678090113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2855195258294791232961205 267674555465136678090113)
                    ·
                      rfl

theorem cell23_1563883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 5].length) (baseStart_1563883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563883 prefixEnd_1563883 := by exact prefixLift 1563883
  have htrace : WordTrace (prefixWord ++ tailWord_1563883) baseStart_1563883 baseEnd_1563883 := by
    simpa [prefixWord, tailWord_1563883, baseEnd_1563883] using wordTrace_append hprefix tailTrace_1563883
  have hstable : (prefixWord ++ tailWord_1563883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563883).length < 2 ^ (prefixWord ++ tailWord_1563883).sum := by decide
  have hdescent : baseEnd_1563883 < baseStart_1563883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563903 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 2, 4, 2]
def baseStart_1563903 : Nat := 118140960795 + 1563903 * 2 ^ 59
def prefixEnd_1563903 : Nat := 4983230072969 + 3 ^ 40 * 1563903 * 2
def baseEnd_1563903 : Nat := 803033936008499956020247

theorem tailTrace_1563903 : CollatzResearch.WordTrace tailWord_1563903 prefixEnd_1563903 803033936008499956020247 := by
  unfold tailWord_1563903
  simp only [CollatzResearch.WordTrace]
  refine ⟨57040228453253999213120363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38026818968835999475413575 57040228453253999213120363)
  ·
    refine ⟨85560342679880998819680545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57040228453253999213120363 85560342679880998819680545)
    ·
      refine ⟨64170257009910749114760409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85560342679880998819680545 64170257009910749114760409)
      ·
        refine ⟨48127692757433061836070307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64170257009910749114760409 48127692757433061836070307)
        ·
          refine ⟨72191539136149592754105461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48127692757433061836070307 72191539136149592754105461)
          ·
            refine ⟨6767956794014024320697387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72191539136149592754105461 6767956794014024320697387)
            ·
              refine ⟨10151935191021036481046081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767956794014024320697387 10151935191021036481046081)
              ·
                refine ⟨7613951393265777360784561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10151935191021036481046081 7613951393265777360784561)
                ·
                  refine ⟨5710463544949333020588421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613951393265777360784561 5710463544949333020588421)
                  ·
                    refine ⟨1070711914677999941360329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5710463544949333020588421 1070711914677999941360329)
                    ·
                      refine ⟨803033936008499956020247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070711914677999941360329 803033936008499956020247)
                      ·
                        rfl

theorem cell23_1563903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_1563903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563903 prefixEnd_1563903 := by exact prefixLift 1563903
  have htrace : WordTrace (prefixWord ++ tailWord_1563903) baseStart_1563903 baseEnd_1563903 := by
    simpa [prefixWord, tailWord_1563903, baseEnd_1563903] using wordTrace_append hprefix tailTrace_1563903
  have hstable : (prefixWord ++ tailWord_1563903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563903).length < 2 ^ (prefixWord ++ tailWord_1563903).sum := by decide
  have hdescent : baseEnd_1563903 < baseStart_1563903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563913 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 3, 4]
def baseStart_1563913 : Nat := 118140960795 + 1563913 * 2 ^ 59
def prefixEnd_1563913 : Nat := 4983230072969 + 3 ^ 40 * 1563913 * 2
def baseEnd_1563913 : Nat := 267679690271681638965067

theorem tailTrace_1563913 : CollatzResearch.WordTrace tailWord_1563913 prefixEnd_1563913 267679690271681638965067 := by
  unfold tailWord_1563913
  simp only [CollatzResearch.WordTrace]
  refine ⟨57040593183217770920984393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38027062122145180613989595 57040593183217770920984393)
  ·
    refine ⟨42780444887413328190738295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57040593183217770920984393 42780444887413328190738295)
    ·
      refine ⟨64170667331119992286107443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42780444887413328190738295 64170667331119992286107443)
      ·
        refine ⟨96256000996679988429161165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64170667331119992286107443 96256000996679988429161165)
        ·
          refine ⟨36096000373754995660935437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96256000996679988429161165 36096000373754995660935437)
          ·
            refine ⟨13536000140158123372850789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36096000373754995660935437 13536000140158123372850789)
            ·
              refine ⟨2538000026279648132409523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13536000140158123372850789 2538000026279648132409523)
              ·
                refine ⟨3807000039419472198614285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538000026279648132409523 3807000039419472198614285)
                ·
                  refine ⟨1427625014782302074480357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3807000039419472198614285 1427625014782302074480357)
                  ·
                    refine ⟨267679690271681638965067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427625014782302074480357 267679690271681638965067)
                    ·
                      rfl

theorem cell23_1563913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_1563913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563913 prefixEnd_1563913 := by exact prefixLift 1563913
  have htrace : WordTrace (prefixWord ++ tailWord_1563913) baseStart_1563913 baseEnd_1563913 := by
    simpa [prefixWord, tailWord_1563913, baseEnd_1563913] using wordTrace_append hprefix tailTrace_1563913
  have hstable : (prefixWord ++ tailWord_1563913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563913).length < 2 ^ (prefixWord ++ tailWord_1563913).sum := by decide
  have hdescent : baseEnd_1563913 < baseStart_1563913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563976 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1563976 : Nat := 118140960795 + 1563976 * 2 ^ 59
def prefixEnd_1563976 : Nat := 4983230072969 + 3 ^ 40 * 1563976 * 2
def baseEnd_1563976 : Nat := 803071420096278170407411

theorem tailTrace_1563976 : CollatzResearch.WordTrace tailWord_1563976 prefixEnd_1563976 803071420096278170407411 := by
  unfold tailWord_1563976
  simp only [CollatzResearch.WordTrace]
  refine ⟨28521445490994766340263891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38028593987993021787018521 28521445490994766340263891)
  ·
    refine ⟨42782168236492149510395837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28521445490994766340263891 42782168236492149510395837)
    ·
      refine ⟨16043313088684556066398439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42782168236492149510395837 16043313088684556066398439)
      ·
        refine ⟨24064969633026834099597659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16043313088684556066398439 24064969633026834099597659)
        ·
          refine ⟨36097454449540251149396489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24064969633026834099597659 36097454449540251149396489)
          ·
            refine ⟨27073090837155188362047367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36097454449540251149396489 27073090837155188362047367)
            ·
              refine ⟨40609636255732782543071051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27073090837155188362047367 40609636255732782543071051)
              ·
                refine ⟨60914454383599173814606577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40609636255732782543071051 60914454383599173814606577)
                ·
                  refine ⟨45685840787699380360954933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60914454383599173814606577 45685840787699380360954933)
                  ·
                    refine ⟨4283047573846816908839525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45685840787699380360954933 4283047573846816908839525)
                    ·
                      refine ⟨803071420096278170407411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4283047573846816908839525 803071420096278170407411)
                      ·
                        rfl

theorem cell23_1563976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1563976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563976 prefixEnd_1563976 := by exact prefixLift 1563976
  have htrace : WordTrace (prefixWord ++ tailWord_1563976) baseStart_1563976 baseEnd_1563976 := by
    simpa [prefixWord, tailWord_1563976, baseEnd_1563976] using wordTrace_append hprefix tailTrace_1563976
  have hstable : (prefixWord ++ tailWord_1563976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563976).length < 2 ^ (prefixWord ++ tailWord_1563976).sum := by decide
  have hdescent : baseEnd_1563976 < baseStart_1563976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563993 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 6, 2]
def baseStart_1563993 : Nat := 118140960795 + 1563993 * 2 ^ 59
def prefixEnd_1563993 : Nat := 4983230072969 + 3 ^ 40 * 1563993 * 2
def baseEnd_1563993 : Nat := 803080149267404603894833

theorem tailTrace_1563993 : CollatzResearch.WordTrace tailWord_1563993 prefixEnd_1563993 803080149267404603894833 := by
  unfold tailWord_1563993
  simp only [CollatzResearch.WordTrace]
  refine ⟨57043511022927944583896633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38029007348618629722597755 57043511022927944583896633)
  ·
    refine ⟨42782633267195958437922475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57043511022927944583896633 42782633267195958437922475)
    ·
      refine ⟨64173949900793937656883713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42782633267195958437922475 64173949900793937656883713)
      ·
        refine ⟨48130462425595453242662785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64173949900793937656883713 48130462425595453242662785)
        ·
          refine ⟨36097846819196589931997089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48130462425595453242662785 36097846819196589931997089)
          ·
            refine ⟨27073385114397442448997817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36097846819196589931997089 27073385114397442448997817)
            ·
              refine ⟨20305038835798081836748363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27073385114397442448997817 20305038835798081836748363)
              ·
                refine ⟨30457558253697122755122545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20305038835798081836748363 30457558253697122755122545)
                ·
                  refine ⟨22843168690272842066341909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30457558253697122755122545 22843168690272842066341909)
                  ·
                    refine ⟨1070773532356539471859777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22843168690272842066341909 1070773532356539471859777)
                    ·
                      refine ⟨803080149267404603894833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070773532356539471859777 803080149267404603894833)
                      ·
                        rfl

theorem cell23_1563993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_1563993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1563993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1563993 prefixEnd_1563993 := by exact prefixLift 1563993
  have htrace : WordTrace (prefixWord ++ tailWord_1563993) baseStart_1563993 baseEnd_1563993 := by
    simpa [prefixWord, tailWord_1563993, baseEnd_1563993] using wordTrace_append hprefix tailTrace_1563993
  have hstable : (prefixWord ++ tailWord_1563993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563993).length < 2 ^ (prefixWord ++ tailWord_1563993).sum := by decide
  have hdescent : baseEnd_1563993 < baseStart_1563993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564003 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 1, 6]
def baseStart_1564003 : Nat := 118140960795 + 1564003 * 2 ^ 59
def prefixEnd_1564003 : Nat := 4983230072969 + 3 ^ 40 * 1564003 * 2
def baseEnd_1564003 : Nat := 267695094691316521589929

theorem tailTrace_1564003 : CollatzResearch.WordTrace tailWord_1564003 prefixEnd_1564003 267695094691316521589929 := by
  unfold tailWord_1564003
  simp only [CollatzResearch.WordTrace]
  refine ⟨57043875752891716291760663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38029250501927810861173775 57043875752891716291760663)
  ·
    refine ⟨85565813629337574437640995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57043875752891716291760663 85565813629337574437640995)
    ·
      refine ⟨128348720444006361656461493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85565813629337574437640995 128348720444006361656461493)
      ·
        refine ⟨12032692541625596405293265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128348720444006361656461493 12032692541625596405293265)
        ·
          refine ⟨9024519406219197303969949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12032692541625596405293265 9024519406219197303969949)
          ·
            refine ⟨3384194777332198988988731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9024519406219197303969949 3384194777332198988988731)
            ·
              refine ⟨5076292165998298483483097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384194777332198988988731 5076292165998298483483097)
              ·
                refine ⟨3807219124498723862612323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076292165998298483483097 3807219124498723862612323)
                ·
                  refine ⟨5710828686748085793918485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807219124498723862612323 5710828686748085793918485)
                  ·
                    refine ⟨267695094691316521589929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5710828686748085793918485 267695094691316521589929)
                    ·
                      rfl

theorem cell23_1564003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 6].length) (baseStart_1564003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564003 prefixEnd_1564003 := by exact prefixLift 1564003
  have htrace : WordTrace (prefixWord ++ tailWord_1564003) baseStart_1564003 baseEnd_1564003 := by
    simpa [prefixWord, tailWord_1564003, baseEnd_1564003] using wordTrace_append hprefix tailTrace_1564003
  have hstable : (prefixWord ++ tailWord_1564003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564003).length < 2 ^ (prefixWord ++ tailWord_1564003).sum := by decide
  have hdescent : baseEnd_1564003 < baseStart_1564003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564007 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 1, 5]
def baseStart_1564007 : Nat := 118140960795 + 1564007 * 2 ^ 59
def prefixEnd_1564007 : Nat := 4983230072969 + 3 ^ 40 * 1564007 * 2
def baseEnd_1564007 : Nat := 267695779332189183039923

theorem tailTrace_1564007 : CollatzResearch.WordTrace tailWord_1564007 prefixEnd_1564007 267695779332189183039923 := by
  unfold tailWord_1564007
  simp only [CollatzResearch.WordTrace]
  refine ⟨57044021644877224974906275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38029347763251483316604183 57044021644877224974906275)
  ·
    refine ⟨85566032467315837462359413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57044021644877224974906275 85566032467315837462359413)
    ·
      refine ⟨8021815543810859762096195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85566032467315837462359413 8021815543810859762096195)
      ·
        refine ⟨12032723315716289643144293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8021815543810859762096195 12032723315716289643144293)
        ·
          refine ⟨2256135621696804308089555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12032723315716289643144293 2256135621696804308089555)
          ·
            refine ⟨3384203432545206462134333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256135621696804308089555 3384203432545206462134333)
            ·
              refine ⟨1269076287204452423300375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3384203432545206462134333 1269076287204452423300375)
              ·
                refine ⟨1903614430806678634950563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269076287204452423300375 1903614430806678634950563)
                ·
                  refine ⟨2855421646210017952425845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903614430806678634950563 2855421646210017952425845)
                  ·
                    refine ⟨267695779332189183039923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2855421646210017952425845 267695779332189183039923)
                    ·
                      rfl

theorem cell23_1564007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_1564007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564007 prefixEnd_1564007 := by exact prefixLift 1564007
  have htrace : WordTrace (prefixWord ++ tailWord_1564007) baseStart_1564007 baseEnd_1564007 := by
    simpa [prefixWord, tailWord_1564007, baseEnd_1564007] using wordTrace_append hprefix tailTrace_1564007
  have hstable : (prefixWord ++ tailWord_1564007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564007).length < 2 ^ (prefixWord ++ tailWord_1564007).sum := by decide
  have hdescent : baseEnd_1564007 < baseStart_1564007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564040 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1564040 : Nat := 118140960795 + 1564040 * 2 ^ 59
def prefixEnd_1564040 : Nat := 4983230072969 + 3 ^ 40 * 1564040 * 2
def baseEnd_1564040 : Nat := 803104282858165920007117

theorem tailTrace_1564040 : CollatzResearch.WordTrace tailWord_1564040 prefixEnd_1564040 803104282858165920007117 := by
  unfold tailWord_1564040
  simp only [CollatzResearch.WordTrace]
  refine ⟨28522612626878835805428787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38030150169171781073905049 28522612626878835805428787)
  ·
    refine ⟨42783918940318253708143181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28522612626878835805428787 42783918940318253708143181)
    ·
      refine ⟨16043969602619345140553693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42783918940318253708143181 16043969602619345140553693)
      ·
        refine ⟨6016488600982254427707635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16043969602619345140553693 6016488600982254427707635)
        ·
          refine ⟨9024732901473381641561453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016488600982254427707635 9024732901473381641561453)
          ·
            refine ⟨3384274838052518115585545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9024732901473381641561453 3384274838052518115585545)
            ·
              refine ⟨2538206128539388586689159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384274838052518115585545 2538206128539388586689159)
              ·
                refine ⟨3807309192809082880033739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538206128539388586689159 3807309192809082880033739)
                ·
                  refine ⟨5710963789213624320050609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807309192809082880033739 5710963789213624320050609)
                  ·
                    refine ⟨4283222841910218240037957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710963789213624320050609 4283222841910218240037957)
                    ·
                      refine ⟨803104282858165920007117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4283222841910218240037957 803104282858165920007117)
                      ·
                        rfl

theorem cell23_1564040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1564040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564040 prefixEnd_1564040 := by exact prefixLift 1564040
  have htrace : WordTrace (prefixWord ++ tailWord_1564040) baseStart_1564040 baseEnd_1564040 := by
    simpa [prefixWord, tailWord_1564040, baseEnd_1564040] using wordTrace_append hprefix tailTrace_1564040
  have hstable : (prefixWord ++ tailWord_1564040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564040).length < 2 ^ (prefixWord ++ tailWord_1564040).sum := by decide
  have hdescent : baseEnd_1564040 < baseStart_1564040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564061 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_1564061 : Nat := 118140960795 + 1564061 * 2 ^ 59
def prefixEnd_1564061 : Nat := 4983230072969 + 3 ^ 40 * 1564061 * 2
def baseEnd_1564061 : Nat := 803115065951910337844521

theorem tailTrace_1564061 : CollatzResearch.WordTrace tailWord_1564061 prefixEnd_1564061 803115065951910337844521 := by
  unfold tailWord_1564061
  simp only [CollatzResearch.WordTrace]
  refine ⟨57045991186681592197372037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38030660791121061464914691 57045991186681592197372037)
  ·
    refine ⟨10696123347502798537007257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57045991186681592197372037 10696123347502798537007257)
    ·
      refine ⟨8022092510627098902755443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10696123347502798537007257 8022092510627098902755443)
      ·
        refine ⟨12033138765940648354133165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022092510627098902755443 12033138765940648354133165)
        ·
          refine ⟨4512427037227743132799937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12033138765940648354133165 4512427037227743132799937)
          ·
            refine ⟨3384320277920807349599953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4512427037227743132799937 3384320277920807349599953)
            ·
              refine ⟨2538240208440605512199965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384320277920807349599953 2538240208440605512199965)
              ·
                refine ⟨951840078165227067074987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2538240208440605512199965 951840078165227067074987)
                ·
                  refine ⟨1427760117247840600612481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951840078165227067074987 1427760117247840600612481)
                  ·
                    refine ⟨1070820087935880450459361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1427760117247840600612481 1070820087935880450459361)
                    ·
                      refine ⟨803115065951910337844521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070820087935880450459361 803115065951910337844521)
                      ·
                        rfl

theorem cell23_1564061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_1564061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564061 prefixEnd_1564061 := by exact prefixLift 1564061
  have htrace : WordTrace (prefixWord ++ tailWord_1564061) baseStart_1564061 baseEnd_1564061 := by
    simpa [prefixWord, tailWord_1564061, baseEnd_1564061] using wordTrace_append hprefix tailTrace_1564061
  have hstable : (prefixWord ++ tailWord_1564061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564061).length < 2 ^ (prefixWord ++ tailWord_1564061).sum := by decide
  have hdescent : baseEnd_1564061 < baseStart_1564061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564093 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1564093 : Nat := 118140960795 + 1564093 * 2 ^ 59
def prefixEnd_1564093 : Nat := 4983230072969 + 3 ^ 40 * 1564093 * 2
def baseEnd_1564093 : Nat := 267710499110951404214791

theorem tailTrace_1564093 : CollatzResearch.WordTrace tailWord_1564093 prefixEnd_1564093 267710499110951404214791 := by
  unfold tailWord_1564093
  simp only [CollatzResearch.WordTrace]
  refine ⟨57047158322565661662536933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38031438881710441108357955 57047158322565661662536933)
  ·
    refine ⟨10696342185481061561725675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57047158322565661662536933 10696342185481061561725675)
    ·
      refine ⟨16044513278221592342588513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10696342185481061561725675 16044513278221592342588513)
      ·
        refine ⟨12033384958666194256941385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16044513278221592342588513 12033384958666194256941385)
        ·
          refine ⟨9025038718999645692706039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033384958666194256941385 9025038718999645692706039)
          ·
            refine ⟨13537558078499468539059059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025038718999645692706039 13537558078499468539059059)
            ·
              refine ⟨20306337117749202808588589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13537558078499468539059059 20306337117749202808588589)
              ·
                refine ⟨7614876419155951053220721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20306337117749202808588589 7614876419155951053220721)
                ·
                  refine ⟨5711157314366963289915541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7614876419155951053220721 5711157314366963289915541)
                  ·
                    refine ⟨267710499110951404214791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5711157314366963289915541 267710499110951404214791)
                    ·
                      rfl

theorem cell23_1564093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1564093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564093 prefixEnd_1564093 := by exact prefixLift 1564093
  have htrace : WordTrace (prefixWord ++ tailWord_1564093) baseStart_1564093 baseEnd_1564093 := by
    simpa [prefixWord, tailWord_1564093, baseEnd_1564093] using wordTrace_append hprefix tailTrace_1564093
  have hstable : (prefixWord ++ tailWord_1564093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564093).length < 2 ^ (prefixWord ++ tailWord_1564093).sum := by decide
  have hdescent : baseEnd_1564093 < baseStart_1564093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564103 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1564103 : Nat := 118140960795 + 1564103 * 2 ^ 59
def prefixEnd_1564103 : Nat := 4983230072969 + 3 ^ 40 * 1564103 * 2
def baseEnd_1564103 : Nat := 803136632139399173519327

theorem tailTrace_1564103 : CollatzResearch.WordTrace tailWord_1564103 prefixEnd_1564103 803136632139399173519327 := by
  unfold tailWord_1564103
  simp only [CollatzResearch.WordTrace]
  refine ⟨57047523052529433370400963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38031682035019622246933975 57047523052529433370400963)
  ·
    refine ⟨85571284578794150055601445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57047523052529433370400963 85571284578794150055601445)
    ·
      refine ⟨16044615858523903135425271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85571284578794150055601445 16044615858523903135425271)
      ·
        refine ⟨24066923787785854703137907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16044615858523903135425271 24066923787785854703137907)
        ·
          refine ⟨36100385681678782054706861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24066923787785854703137907 36100385681678782054706861)
          ·
            refine ⟨13537644630629543270515073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36100385681678782054706861 13537644630629543270515073)
            ·
              refine ⟨10153233472972157452886305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13537644630629543270515073 10153233472972157452886305)
              ·
                refine ⟨7614925104729118089664729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10153233472972157452886305 7614925104729118089664729)
                ·
                  refine ⟨5711193828546838567248547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7614925104729118089664729 5711193828546838567248547)
                  ·
                    refine ⟨8566790742820257850872821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5711193828546838567248547 8566790742820257850872821)
                    ·
                      refine ⟨803136632139399173519327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8566790742820257850872821 803136632139399173519327)
                      ·
                        rfl

theorem cell23_1564103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1564103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564103 prefixEnd_1564103 := by exact prefixLift 1564103
  have htrace : WordTrace (prefixWord ++ tailWord_1564103) baseStart_1564103 baseEnd_1564103 := by
    simpa [prefixWord, tailWord_1564103, baseEnd_1564103] using wordTrace_append hprefix tailTrace_1564103
  have hstable : (prefixWord ++ tailWord_1564103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564103).length < 2 ^ (prefixWord ++ tailWord_1564103).sum := by decide
  have hdescent : baseEnd_1564103 < baseStart_1564103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564117 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1564117 : Nat := 118140960795 + 1564117 * 2 ^ 59
def prefixEnd_1564117 : Nat := 4983230072969 + 3 ^ 40 * 1564117 * 2
def baseEnd_1564117 : Nat := 803143820868562118744263

theorem tailTrace_1564117 : CollatzResearch.WordTrace tailWord_1564117 prefixEnd_1564117 803143820868562118744263 := by
  unfold tailWord_1564117
  simp only [CollatzResearch.WordTrace]
  refine ⟨57048033674478713761410605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38032022449652475840940403 57048033674478713761410605)
  ·
    refine ⟨21393012627929517660528977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57048033674478713761410605 21393012627929517660528977)
    ·
      refine ⟨16044759470947138245396733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21393012627929517660528977 16044759470947138245396733)
      ·
        refine ⟨6016784801605176842023775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16044759470947138245396733 6016784801605176842023775)
        ·
          refine ⟨9025177202407765263035663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016784801605176842023775 9025177202407765263035663)
          ·
            refine ⟨13537765803611647894553495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025177202407765263035663 13537765803611647894553495)
            ·
              refine ⟨20306648705417471841830243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13537765803611647894553495 20306648705417471841830243)
              ·
                refine ⟨30459973058126207762745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20306648705417471841830243 30459973058126207762745365)
                ·
                  refine ⟨1427811237099665988878689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30459973058126207762745365 1427811237099665988878689)
                  ·
                    refine ⟨1070858427824749491659017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1427811237099665988878689 1070858427824749491659017)
                    ·
                      refine ⟨803143820868562118744263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1070858427824749491659017 803143820868562118744263)
                      ·
                        rfl

theorem cell23_1564117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1564117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564117 prefixEnd_1564117 := by exact prefixLift 1564117
  have htrace : WordTrace (prefixWord ++ tailWord_1564117) baseStart_1564117 baseEnd_1564117 := by
    simpa [prefixWord, tailWord_1564117, baseEnd_1564117] using wordTrace_append hprefix tailTrace_1564117
  have hstable : (prefixWord ++ tailWord_1564117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564117).length < 2 ^ (prefixWord ++ tailWord_1564117).sum := by decide
  have hdescent : baseEnd_1564117 < baseStart_1564117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564153 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_1564153 : Nat := 118140960795 + 1564153 * 2 ^ 59
def prefixEnd_1564153 : Nat := 4983230072969 + 3 ^ 40 * 1564153 * 2
def baseEnd_1564153 : Nat := 267720768724041325964699

theorem tailTrace_1564153 : CollatzResearch.WordTrace tailWord_1564153 prefixEnd_1564153 267720768724041325964699 := by
  unfold tailWord_1564153
  simp only [CollatzResearch.WordTrace]
  refine ⟨57049346702348291909721113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38032897801565527939814075 57049346702348291909721113)
  ·
    refine ⟨42787010026761218932290835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57049346702348291909721113 42787010026761218932290835)
    ·
      refine ⟨64180515040141828398436253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42787010026761218932290835 64180515040141828398436253)
      ·
        refine ⟨24067693140053185649413595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64180515040141828398436253 24067693140053185649413595)
        ·
          refine ⟨36101539710079778474120393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24067693140053185649413595 36101539710079778474120393)
          ·
            refine ⟨27076154782559833855590295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36101539710079778474120393 27076154782559833855590295)
            ·
              refine ⟨40614232173839750783385443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27076154782559833855590295 40614232173839750783385443)
              ·
                refine ⟨60921348260759626175078165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40614232173839750783385443 60921348260759626175078165)
                ·
                  refine ⟨2855688199723107476956789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60921348260759626175078165 2855688199723107476956789)
                  ·
                    refine ⟨267720768724041325964699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2855688199723107476956789 267720768724041325964699)
                    ·
                      rfl

theorem cell23_1564153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_1564153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564153 prefixEnd_1564153 := by exact prefixLift 1564153
  have htrace : WordTrace (prefixWord ++ tailWord_1564153) baseStart_1564153 baseEnd_1564153 := by
    simpa [prefixWord, tailWord_1564153, baseEnd_1564153] using wordTrace_append hprefix tailTrace_1564153
  have hstable : (prefixWord ++ tailWord_1564153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564153).length < 2 ^ (prefixWord ++ tailWord_1564153).sum := by decide
  have hdescent : baseEnd_1564153 < baseStart_1564153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564170 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1564170 : Nat := 118140960795 + 1564170 * 2 ^ 59
def prefixEnd_1564170 : Nat := 4983230072969 + 3 ^ 40 * 1564170 * 2
def baseEnd_1564170 : Nat := 267723678447750137127173

theorem tailTrace_1564170 : CollatzResearch.WordTrace tailWord_1564170 prefixEnd_1564170 267723678447750137127173 := by
  unfold tailWord_1564170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262491685821675953272491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38033311162191135875393309 14262491685821675953272491)
  ·
    refine ⟨21393737528732513929908737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14262491685821675953272491 21393737528732513929908737)
    ·
      refine ⟨16045303146549385447431553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21393737528732513929908737 16045303146549385447431553)
      ·
        refine ⟨12033977359912039085573665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16045303146549385447431553 12033977359912039085573665)
        ·
          refine ⟨9025483019934029314180249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033977359912039085573665 9025483019934029314180249)
          ·
            refine ⟨6769112264950521985635187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9025483019934029314180249 6769112264950521985635187)
            ·
              refine ⟨10153668397425782978452781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769112264950521985635187 10153668397425782978452781)
              ·
                refine ⟨3807625649034668616919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10153668397425782978452781 3807625649034668616919793)
                ·
                  refine ⟨2855719236776001462689845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3807625649034668616919793 2855719236776001462689845)
                  ·
                    refine ⟨267723678447750137127173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2855719236776001462689845 267723678447750137127173)
                    ·
                      rfl

theorem cell23_1564170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1564170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564170 prefixEnd_1564170 := by exact prefixLift 1564170
  have htrace : WordTrace (prefixWord ++ tailWord_1564170) baseStart_1564170 baseEnd_1564170 := by
    simpa [prefixWord, tailWord_1564170, baseEnd_1564170] using wordTrace_append hprefix tailTrace_1564170
  have hstable : (prefixWord ++ tailWord_1564170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564170).length < 2 ^ (prefixWord ++ tailWord_1564170).sum := by decide
  have hdescent : baseEnd_1564170 < baseStart_1564170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564203 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4]
def baseStart_1564203 : Nat := 118140960795 + 1564203 * 2 ^ 59
def prefixEnd_1564203 : Nat := 4983230072969 + 3 ^ 40 * 1564203 * 2
def baseEnd_1564203 : Nat := 803187980204848782268867

theorem tailTrace_1564203 : CollatzResearch.WordTrace tailWord_1564203 prefixEnd_1564203 803187980204848782268867 := by
  unfold tailWord_1564203
  simp only [CollatzResearch.WordTrace]
  refine ⟨57051170352167150449041263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38034113568111433632694175 57051170352167150449041263)
  ·
    refine ⟨85576755528250725673561895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57051170352167150449041263 85576755528250725673561895)
    ·
      refine ⟨128365133292376088510342843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85576755528250725673561895 128365133292376088510342843)
      ·
        refine ⟨192547699938564132765514265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128365133292376088510342843 192547699938564132765514265)
        ·
          refine ⟨144410774953923099574135699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192547699938564132765514265 144410774953923099574135699)
          ·
            refine ⟨216616162430884649361203549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144410774953923099574135699 216616162430884649361203549)
            ·
              refine ⟨81231060911581743510451331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216616162430884649361203549 81231060911581743510451331)
              ·
                refine ⟨121846591367372615265676997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81231060911581743510451331 121846591367372615265676997)
                ·
                  refine ⟨22846235881382365362314437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121846591367372615265676997 22846235881382365362314437)
                  ·
                    refine ⟨4283669227759193505433957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22846235881382365362314437 4283669227759193505433957)
                    ·
                      refine ⟨803187980204848782268867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4283669227759193505433957 803187980204848782268867)
                      ·
                        rfl

theorem cell23_1564203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_1564203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564203 prefixEnd_1564203 := by exact prefixLift 1564203
  have htrace : WordTrace (prefixWord ++ tailWord_1564203) baseStart_1564203 baseEnd_1564203 := by
    simpa [prefixWord, tailWord_1564203, baseEnd_1564203] using wordTrace_append hprefix tailTrace_1564203
  have hstable : (prefixWord ++ tailWord_1564203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564203).length < 2 ^ (prefixWord ++ tailWord_1564203).sum := by decide
  have hdescent : baseEnd_1564203 < baseStart_1564203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564210 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1564210 : Nat := 118140960795 + 1564210 * 2 ^ 59
def prefixEnd_1564210 : Nat := 4983230072969 + 3 ^ 40 * 1564210 * 2
def baseEnd_1564210 : Nat := 803191574569430254881335

theorem tailTrace_1564210 : CollatzResearch.WordTrace tailWord_1564210 prefixEnd_1564210 803191574569430254881335 := by
  unfold tailWord_1564210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262856415785447661136521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38034283775427860429697389 14262856415785447661136521)
  ·
    refine ⟨10697142311839085745852391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14262856415785447661136521 10697142311839085745852391)
    ·
      refine ⟨16045713467758628618778587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10697142311839085745852391 16045713467758628618778587)
      ·
        refine ⟨24068570201637942928167881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16045713467758628618778587 24068570201637942928167881)
        ·
          refine ⟨18051427651228457196125911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24068570201637942928167881 18051427651228457196125911)
          ·
            refine ⟨27077141476842685794188867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18051427651228457196125911 27077141476842685794188867)
            ·
              refine ⟨40615712215264028691283301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27077141476842685794188867 40615712215264028691283301)
              ·
                refine ⟨7615446040362005379615619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40615712215264028691283301 7615446040362005379615619)
                ·
                  refine ⟨11423169060543008069423429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7615446040362005379615619 11423169060543008069423429)
                  ·
                    refine ⟨2141844198851814013016893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11423169060543008069423429 2141844198851814013016893)
                    ·
                      refine ⟨803191574569430254881335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2141844198851814013016893 803191574569430254881335)
                      ·
                        rfl

theorem cell23_1564210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1564210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564210 prefixEnd_1564210 := by exact prefixLift 1564210
  have htrace : WordTrace (prefixWord ++ tailWord_1564210) baseStart_1564210 baseEnd_1564210 := by
    simpa [prefixWord, tailWord_1564210, baseEnd_1564210] using wordTrace_append hprefix tailTrace_1564210
  have hstable : (prefixWord ++ tailWord_1564210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564210).length < 2 ^ (prefixWord ++ tailWord_1564210).sum := by decide
  have hdescent : baseEnd_1564210 < baseStart_1564210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564217 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 3, 4]
def baseStart_1564217 : Nat := 118140960795 + 1564217 * 2 ^ 59
def prefixEnd_1564217 : Nat := 4983230072969 + 3 ^ 40 * 1564217 * 2
def baseEnd_1564217 : Nat := 267731722978003909164601

theorem tailTrace_1564217 : CollatzResearch.WordTrace tailWord_1564217 prefixEnd_1564217 267731722978003909164601 := by
  unfold tailWord_1564217
  simp only [CollatzResearch.WordTrace]
  refine ⟨57051680974116430840050905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38034453982744287226700603 57051680974116430840050905)
  ·
    refine ⟨42788760730587323130038179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57051680974116430840050905 42788760730587323130038179)
    ·
      refine ⟨64183141095880984695057269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42788760730587323130038179 64183141095880984695057269)
      ·
        refine ⟨6017169477738842315161619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64183141095880984695057269 6017169477738842315161619)
        ·
          refine ⟨9025754216608263472742429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017169477738842315161619 9025754216608263472742429)
          ·
            refine ⟨3384657831228098802278411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9025754216608263472742429 3384657831228098802278411)
            ·
              refine ⟨5076986746842148203417617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384657831228098802278411 5076986746842148203417617)
              ·
                refine ⟨3807740060131611152563213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076986746842148203417617 3807740060131611152563213)
                ·
                  refine ⟨1427902522549354182211205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3807740060131611152563213 1427902522549354182211205)
                  ·
                    refine ⟨267731722978003909164601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427902522549354182211205 267731722978003909164601)
                    ·
                      rfl

theorem cell23_1564217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_1564217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564217 prefixEnd_1564217 := by exact prefixLift 1564217
  have htrace : WordTrace (prefixWord ++ tailWord_1564217) baseStart_1564217 baseEnd_1564217 := by
    simpa [prefixWord, tailWord_1564217, baseEnd_1564217] using wordTrace_append hprefix tailTrace_1564217
  have hstable : (prefixWord ++ tailWord_1564217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564217).length < 2 ^ (prefixWord ++ tailWord_1564217).sum := by decide
  have hdescent : baseEnd_1564217 < baseStart_1564217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564233 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_1564233 : Nat := 118140960795 + 1564233 * 2 ^ 59
def prefixEnd_1564233 : Nat := 4983230072969 + 3 ^ 40 * 1564233 * 2
def baseEnd_1564233 : Nat := 803203384624483664893729

theorem tailTrace_1564233 : CollatzResearch.WordTrace tailWord_1564233 prefixEnd_1564233 803203384624483664893729 := by
  unfold tailWord_1564233
  simp only [CollatzResearch.WordTrace]
  refine ⟨57052264542058465572633353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38034843028038977048422235 57052264542058465572633353)
  ·
    refine ⟨42789198406543849179475015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57052264542058465572633353 42789198406543849179475015)
    ·
      refine ⟨64183797609815773769212523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42789198406543849179475015 64183797609815773769212523)
      ·
        refine ⟨96275696414723660653818785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64183797609815773769212523 96275696414723660653818785)
        ·
          refine ⟨72206772311042745490364089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96275696414723660653818785 72206772311042745490364089)
          ·
            refine ⟨54155079233282059117773067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72206772311042745490364089 54155079233282059117773067)
            ·
              refine ⟨81232618849923088676659601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54155079233282059117773067 81232618849923088676659601)
              ·
                refine ⟨60924464137442316507494701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81232618849923088676659601 60924464137442316507494701)
                ·
                  refine ⟨22846674051540868690310513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60924464137442316507494701 22846674051540868690310513)
                  ·
                    refine ⟨17135005538655651517732885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22846674051540868690310513 17135005538655651517732885)
                    ·
                      refine ⟨803203384624483664893729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17135005538655651517732885 803203384624483664893729)
                      ·
                        rfl

theorem cell23_1564233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_1564233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564233 prefixEnd_1564233 := by exact prefixLift 1564233
  have htrace : WordTrace (prefixWord ++ tailWord_1564233) baseStart_1564233 baseEnd_1564233 := by
    simpa [prefixWord, tailWord_1564233, baseEnd_1564233] using wordTrace_append hprefix tailTrace_1564233
  have hstable : (prefixWord ++ tailWord_1564233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564233).length < 2 ^ (prefixWord ++ tailWord_1564233).sum := by decide
  have hdescent : baseEnd_1564233 < baseStart_1564233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564234 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_1564234 : Nat := 118140960795 + 1564234 * 2 ^ 59
def prefixEnd_1564234 : Nat := 4983230072969 + 3 ^ 40 * 1564234 * 2
def baseEnd_1564234 : Nat := 267734632701712720327075

theorem tailTrace_1564234 : CollatzResearch.WordTrace tailWord_1564234 prefixEnd_1564234 267734632701712720327075 := by
  unfold tailWord_1564234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263075253763710685854939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38034867343369895162279837 14263075253763710685854939)
  ·
    refine ⟨21394612880645566028782409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14263075253763710685854939 21394612880645566028782409)
    ·
      refine ⟨16045959660484174521586807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21394612880645566028782409 16045959660484174521586807)
      ·
        refine ⟨24068939490726261782380211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16045959660484174521586807 24068939490726261782380211)
        ·
          refine ⟨36103409236089392673570317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24068939490726261782380211 36103409236089392673570317)
          ·
            refine ⟨13538778463533522252588869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36103409236089392673570317 13538778463533522252588869)
            ·
              refine ⟨2538520961912535422360413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13538778463533522252588869 2538520961912535422360413)
              ·
                refine ⟨951945360717200783385155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2538520961912535422360413 951945360717200783385155)
                ·
                  refine ⟨1427918041075801175077733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951945360717200783385155 1427918041075801175077733)
                  ·
                    refine ⟨267734632701712720327075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427918041075801175077733 267734632701712720327075)
                    ·
                      rfl

theorem cell23_1564234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_1564234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564234 prefixEnd_1564234 := by exact prefixLift 1564234
  have htrace : WordTrace (prefixWord ++ tailWord_1564234) baseStart_1564234 baseEnd_1564234 := by
    simpa [prefixWord, tailWord_1564234, baseEnd_1564234] using wordTrace_append hprefix tailTrace_1564234
  have hstable : (prefixWord ++ tailWord_1564234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564234).length < 2 ^ (prefixWord ++ tailWord_1564234).sum := by decide
  have hdescent : baseEnd_1564234 < baseStart_1564234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564247 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 6]
def baseStart_1564247 : Nat := 118140960795 + 1564247 * 2 ^ 59
def prefixEnd_1564247 : Nat := 4983230072969 + 3 ^ 40 * 1564247 * 2
def baseEnd_1564247 : Nat := 89245619261516290013185

theorem tailTrace_1564247 : CollatzResearch.WordTrace tailWord_1564247 prefixEnd_1564247 89245619261516290013185 := by
  unfold tailWord_1564247
  simp only [CollatzResearch.WordTrace]
  refine ⟨57052775164007745963642995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38035183442671830642428663 57052775164007745963642995)
  ·
    refine ⟨85579162746011618945464493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57052775164007745963642995 85579162746011618945464493)
    ·
      refine ⟨32092186029754357104549185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85579162746011618945464493 32092186029754357104549185)
      ·
        refine ⟨24069139522315767828411889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32092186029754357104549185 24069139522315767828411889)
        ·
          refine ⟨18051854641736825871308917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24069139522315767828411889 18051854641736825871308917)
          ·
            refine ⟨1692361372662827425435211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18051854641736825871308917 1692361372662827425435211)
            ·
              refine ⟨2538542058994241138152817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692361372662827425435211 2538542058994241138152817)
              ·
                refine ⟨1903906544245680853614613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538542058994241138152817 1903906544245680853614613)
                ·
                  refine ⟨89245619261516290013185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1903906544245680853614613 89245619261516290013185)
                  ·
                    rfl

theorem cell23_1564247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 6].length) (baseStart_1564247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564247 prefixEnd_1564247 := by exact prefixLift 1564247
  have htrace : WordTrace (prefixWord ++ tailWord_1564247) baseStart_1564247 baseEnd_1564247 := by
    simpa [prefixWord, tailWord_1564247, baseEnd_1564247] using wordTrace_append hprefix tailTrace_1564247
  have hstable : (prefixWord ++ tailWord_1564247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564247).length < 2 ^ (prefixWord ++ tailWord_1564247).sum := by decide
  have hdescent : baseEnd_1564247 < baseStart_1564247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564264 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 6]
def baseStart_1564264 : Nat := 118140960795 + 1564264 * 2 ^ 59
def prefixEnd_1564264 : Nat := 4983230072969 + 3 ^ 40 * 1564264 * 2
def baseEnd_1564264 : Nat := 89246589169419227067343

theorem tailTrace_1564264 : CollatzResearch.WordTrace tailWord_1564264 prefixEnd_1564264 89246589169419227067343 := by
  unfold tailWord_1564264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28526697602473078933505923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38035596803297438578007897 28526697602473078933505923)
  ·
    refine ⟨42790046403709618400258885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28526697602473078933505923 42790046403709618400258885)
    ·
      refine ⟨8023133700695553450048541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42790046403709618400258885 8023133700695553450048541)
      ·
        refine ⟨3008675137760832543768203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8023133700695553450048541 3008675137760832543768203)
        ·
          refine ⟨4513012706641248815652305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008675137760832543768203 4513012706641248815652305)
          ·
            refine ⟨3384759529980936611739229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4513012706641248815652305 3384759529980936611739229)
            ·
              refine ⟨1269284823742851229402211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3384759529980936611739229 1269284823742851229402211)
              ·
                refine ⟨1903927235614276844103317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269284823742851229402211 1903927235614276844103317)
                ·
                  refine ⟨89246589169419227067343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1903927235614276844103317 89246589169419227067343)
                  ·
                    rfl

theorem cell23_1564264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 6].length) (baseStart_1564264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564264 prefixEnd_1564264 := by exact prefixLift 1564264
  have htrace : WordTrace (prefixWord ++ tailWord_1564264) baseStart_1564264 baseEnd_1564264 := by
    simpa [prefixWord, tailWord_1564264, baseEnd_1564264] using wordTrace_append hprefix tailTrace_1564264
  have hstable : (prefixWord ++ tailWord_1564264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564264).length < 2 ^ (prefixWord ++ tailWord_1564264).sum := by decide
  have hdescent : baseEnd_1564264 < baseStart_1564264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564274 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1564274 : Nat := 118140960795 + 1564274 * 2 ^ 59
def prefixEnd_1564274 : Nat := 4983230072969 + 3 ^ 40 * 1564274 * 2
def baseEnd_1564274 : Nat := 803224437331318004481041

theorem tailTrace_1564274 : CollatzResearch.WordTrace tailWord_1564274 prefixEnd_1564274 803224437331318004481041 := by
  unfold tailWord_1564274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263439983727482393718969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38035839956606619716583917 14263439983727482393718969)
  ·
    refine ⟨10697579987795611795289227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14263439983727482393718969 10697579987795611795289227)
    ·
      refine ⟨16046369981693417692933841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10697579987795611795289227 16046369981693417692933841)
      ·
        refine ⟨12034777486270063269700381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16046369981693417692933841 12034777486270063269700381)
        ·
          refine ⟨4513041557351273726137643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12034777486270063269700381 4513041557351273726137643)
          ·
            refine ⟨6769562336026910589206465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513041557351273726137643 6769562336026910589206465)
            ·
              refine ⟨5077171752020182941904849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6769562336026910589206465 5077171752020182941904849)
              ·
                refine ⟨3807878814015137206428637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077171752020182941904849 3807878814015137206428637)
                ·
                  refine ⟨1427954555255676452410739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3807878814015137206428637 1427954555255676452410739)
                  ·
                    refine ⟨2141931832883514678616109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1427954555255676452410739 2141931832883514678616109)
                    ·
                      refine ⟨803224437331318004481041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2141931832883514678616109 803224437331318004481041)
                      ·
                        rfl

theorem cell23_1564274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1564274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564274 prefixEnd_1564274 := by exact prefixLift 1564274
  have htrace : WordTrace (prefixWord ++ tailWord_1564274) baseStart_1564274 baseEnd_1564274 := by
    simpa [prefixWord, tailWord_1564274, baseEnd_1564274] using wordTrace_append hprefix tailTrace_1564274
  have hstable : (prefixWord ++ tailWord_1564274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564274).length < 2 ^ (prefixWord ++ tailWord_1564274).sum := by decide
  have hdescent : baseEnd_1564274 < baseStart_1564274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564297 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 4]
def baseStart_1564297 : Nat := 118140960795 + 1564297 * 2 ^ 59
def prefixEnd_1564297 : Nat := 4983230072969 + 3 ^ 40 * 1564297 * 2
def baseEnd_1564297 : Nat := 803236247386371414493435

theorem tailTrace_1564297 : CollatzResearch.WordTrace tailWord_1564297 prefixEnd_1564297 803236247386371414493435 := by
  unfold tailWord_1564297
  simp only [CollatzResearch.WordTrace]
  refine ⟨57054598813826604502963145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38036399209217736335308763 57054598813826604502963145)
  ·
    refine ⟨42790949110369953377222359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57054598813826604502963145 42790949110369953377222359)
    ·
      refine ⟨64186423665554930065833539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42790949110369953377222359 64186423665554930065833539)
      ·
        refine ⟨96279635498332395098750309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64186423665554930065833539 96279635498332395098750309)
        ·
          refine ⟨18052431655937324081015683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96279635498332395098750309 18052431655937324081015683)
          ·
            refine ⟨27078647483905986121523525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18052431655937324081015683 27078647483905986121523525)
            ·
              refine ⟨5077246403232372397785661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27078647483905986121523525 5077246403232372397785661)
              ·
                refine ⟨1903967401212139649169623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5077246403232372397785661 1903967401212139649169623)
                ·
                  refine ⟨2855951101818209473754435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903967401212139649169623 2855951101818209473754435)
                  ·
                    refine ⟨4283926652727314210631653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2855951101818209473754435 4283926652727314210631653)
                    ·
                      refine ⟨803236247386371414493435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4283926652727314210631653 803236247386371414493435)
                      ·
                        rfl

theorem cell23_1564297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_1564297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564297 prefixEnd_1564297 := by exact prefixLift 1564297
  have htrace : WordTrace (prefixWord ++ tailWord_1564297) baseStart_1564297 baseEnd_1564297 := by
    simpa [prefixWord, tailWord_1564297, baseEnd_1564297] using wordTrace_append hprefix tailTrace_1564297
  have hstable : (prefixWord ++ tailWord_1564297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564297).length < 2 ^ (prefixWord ++ tailWord_1564297).sum := by decide
  have hdescent : baseEnd_1564297 < baseStart_1564297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564308 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1564308 : Nat := 118140960795 + 1564308 * 2 ^ 59
def prefixEnd_1564308 : Nat := 4983230072969 + 3 ^ 40 * 1564308 * 2
def baseEnd_1564308 : Nat := 803241895673570871455885

theorem tailTrace_1564308 : CollatzResearch.WordTrace tailWord_1564308 prefixEnd_1564308 803241895673570871455885 := by
  unfold tailWord_1564308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527500008393376690806789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38036666677857835587742385 28527500008393376690806789)
  ·
    refine ⟨5348906251573758129526273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28527500008393376690806789 5348906251573758129526273)
    ·
      refine ⟨4011679688680318597144705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5348906251573758129526273 4011679688680318597144705)
      ·
        refine ⟨3008759766510238947858529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4011679688680318597144705 3008759766510238947858529)
        ·
          refine ⟨2256569824882679210893897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008759766510238947858529 2256569824882679210893897)
          ·
            refine ⟨1692427368662009408170423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256569824882679210893897 1692427368662009408170423)
            ·
              refine ⟨2538641052993014112255635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692427368662009408170423 2538641052993014112255635)
              ·
                refine ⟨3807961579489521168383453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538641052993014112255635 3807961579489521168383453)
                ·
                  refine ⟨1427985592308570438143795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3807961579489521168383453 1427985592308570438143795)
                  ·
                    refine ⟨2141978388462855657215693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1427985592308570438143795 2141978388462855657215693)
                    ·
                      refine ⟨803241895673570871455885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2141978388462855657215693 803241895673570871455885)
                      ·
                        rfl

theorem cell23_1564308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1564308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564308 prefixEnd_1564308 := by exact prefixLift 1564308
  have htrace : WordTrace (prefixWord ++ tailWord_1564308) baseStart_1564308 baseEnd_1564308 := by
    simpa [prefixWord, tailWord_1564308, baseEnd_1564308] using wordTrace_append hprefix tailTrace_1564308
  have hstable : (prefixWord ++ tailWord_1564308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564308).length < 2 ^ (prefixWord ++ tailWord_1564308).sum := by decide
  have hdescent : baseEnd_1564308 < baseStart_1564308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564317 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1564317 : Nat := 118140960795 + 1564317 * 2 ^ 59
def prefixEnd_1564317 : Nat := 4983230072969 + 3 ^ 40 * 1564317 * 2
def baseEnd_1564317 : Nat := 803246516999461336243343

theorem tailTrace_1564317 : CollatzResearch.WordTrace tailWord_1564317 prefixEnd_1564317 803246516999461336243343 := by
  unfold tailWord_1564317
  simp only [CollatzResearch.WordTrace]
  refine ⟨57055328273754147918691205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38036885515836098612460803 57055328273754147918691205)
  ·
    refine ⟨10697874051328902734754601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57055328273754147918691205 10697874051328902734754601)
    ·
      refine ⟨8023405538496677051065951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10697874051328902734754601 8023405538496677051065951)
      ·
        refine ⟨12035108307745015576598927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023405538496677051065951 12035108307745015576598927)
        ·
          refine ⟨18052662461617523364898391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12035108307745015576598927 18052662461617523364898391)
          ·
            refine ⟨27078993692426285047347587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18052662461617523364898391 27078993692426285047347587)
            ·
              refine ⟨40618490538639427571021381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27078993692426285047347587 40618490538639427571021381)
              ·
                refine ⟨7615966975994892669566509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40618490538639427571021381 7615966975994892669566509)
                ·
                  refine ⟨2855987615998084751087441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7615966975994892669566509 2855987615998084751087441)
                  ·
                    refine ⟨2141990711998563563315581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2855987615998084751087441 2141990711998563563315581)
                    ·
                      refine ⟨803246516999461336243343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2141990711998563563315581 803246516999461336243343)
                      ·
                        rfl

theorem cell23_1564317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1564317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564317 prefixEnd_1564317 := by exact prefixLift 1564317
  have htrace : WordTrace (prefixWord ++ tailWord_1564317) baseStart_1564317 baseEnd_1564317 := by
    simpa [prefixWord, tailWord_1564317, baseEnd_1564317] using wordTrace_append hprefix tailTrace_1564317
  have hstable : (prefixWord ++ tailWord_1564317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564317).length < 2 ^ (prefixWord ++ tailWord_1564317).sum := by decide
  have hdescent : baseEnd_1564317 < baseStart_1564317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564320 : List Nat := [2, 1, 1, 4, 3, 1, 1, 10]
def baseStart_1564320 : Nat := 118140960795 + 1564320 * 2 ^ 59
def prefixEnd_1564320 : Nat := 4983230072969 + 3 ^ 40 * 1564320 * 2
def baseEnd_1564320 : Nat := 29749928053386104611327

theorem tailTrace_1564320 : CollatzResearch.WordTrace tailWord_1564320 prefixEnd_1564320 29749928053386104611327 := by
  unfold tailWord_1564320
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527718846371639715525207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38036958461828852954033609 28527718846371639715525207)
  ·
    refine ⟨42791578269557459573287811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28527718846371639715525207 42791578269557459573287811)
    ·
      refine ⟨64187367404336189359931717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42791578269557459573287811 64187367404336189359931717)
      ·
        refine ⟨12035131388313035504987197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64187367404336189359931717 12035131388313035504987197)
        ·
          refine ⟨4513174270617388314370199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12035131388313035504987197 4513174270617388314370199)
          ·
            refine ⟨6769761405926082471555299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513174270617388314370199 6769761405926082471555299)
            ·
              refine ⟨10154642108889123707332949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769761405926082471555299 10154642108889123707332949)
              ·
                refine ⟨29749928053386104611327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10154642108889123707332949 29749928053386104611327)
                ·
                  rfl

theorem cell23_1564320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 10].length) (baseStart_1564320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564320 prefixEnd_1564320 := by exact prefixLift 1564320
  have htrace : WordTrace (prefixWord ++ tailWord_1564320) baseStart_1564320 baseEnd_1564320 := by
    simpa [prefixWord, tailWord_1564320, baseEnd_1564320] using wordTrace_append hprefix tailTrace_1564320
  have hstable : (prefixWord ++ tailWord_1564320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564320).length < 2 ^ (prefixWord ++ tailWord_1564320).sum := by decide
  have hdescent : baseEnd_1564320 < baseStart_1564320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564324 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_1564324 : Nat := 118140960795 + 1564324 * 2 ^ 59
def prefixEnd_1564324 : Nat := 4983230072969 + 3 ^ 40 * 1564324 * 2
def baseEnd_1564324 : Nat := 267750037121347602951937

theorem tailTrace_1564324 : CollatzResearch.WordTrace tailWord_1564324 prefixEnd_1564324 267750037121347602951937 := by
  unfold tailWord_1564324
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527791792364394057098013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38037055723152525409464017 28527791792364394057098013)
  ·
    refine ⟨10697921922136647771411755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28527791792364394057098013 10697921922136647771411755)
    ·
      refine ⟨16046882883204971657117633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10697921922136647771411755 16046882883204971657117633)
      ·
        refine ⟨12035162162403728742838225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16046882883204971657117633 12035162162403728742838225)
        ·
          refine ⟨9026371621802796557128669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12035162162403728742838225 9026371621802796557128669)
          ·
            refine ⟨3384889358176048708923251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9026371621802796557128669 3384889358176048708923251)
            ·
              refine ⟨5077334037264073063384877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384889358176048708923251 5077334037264073063384877)
              ·
                refine ⟨1904000263974027398769329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5077334037264073063384877 1904000263974027398769329)
                ·
                  refine ⟨1428000197980520549076997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904000263974027398769329 1428000197980520549076997)
                  ·
                    refine ⟨267750037121347602951937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428000197980520549076997 267750037121347602951937)
                    ·
                      rfl

theorem cell23_1564324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_1564324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564324 prefixEnd_1564324 := by exact prefixLift 1564324
  have htrace : WordTrace (prefixWord ++ tailWord_1564324) baseStart_1564324 baseEnd_1564324 := by
    simpa [prefixWord, tailWord_1564324, baseEnd_1564324] using wordTrace_append hprefix tailTrace_1564324
  have hstable : (prefixWord ++ tailWord_1564324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564324).length < 2 ^ (prefixWord ++ tailWord_1564324).sum := by decide
  have hdescent : baseEnd_1564324 < baseStart_1564324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564347 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 3]
def baseStart_1564347 : Nat := 118140960795 + 1564347 * 2 ^ 59
def prefixEnd_1564347 : Nat := 4983230072969 + 3 ^ 40 * 1564347 * 2
def baseEnd_1564347 : Nat := 803261921419096218868205

theorem tailTrace_1564347 : CollatzResearch.WordTrace tailWord_1564347 prefixEnd_1564347 803261921419096218868205 := by
  unfold tailWord_1564347
  simp only [CollatzResearch.WordTrace]
  refine ⟨57056422463645463042283295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38037614975763642028188863 57056422463645463042283295)
  ·
    refine ⟨85584633695468194563424943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57056422463645463042283295 85584633695468194563424943)
    ·
      refine ⟨128376950543202291845137415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85584633695468194563424943 128376950543202291845137415)
      ·
        refine ⟨192565425814803437767706123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128376950543202291845137415 192565425814803437767706123)
        ·
          refine ⟨288848138722205156651559185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192565425814803437767706123 288848138722205156651559185)
          ·
            refine ⟨216636104041653867488669389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288848138722205156651559185 216636104041653867488669389)
            ·
              refine ⟨81238539015620200308251021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216636104041653867488669389 81238539015620200308251021)
              ·
                refine ⟨30464452130857575115594133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81238539015620200308251021 30464452130857575115594133)
                ·
                  refine ⟨1428021193633948833543475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30464452130857575115594133 1428021193633948833543475)
                  ·
                    refine ⟨2142031790450923250315213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428021193633948833543475 2142031790450923250315213)
                    ·
                      refine ⟨803261921419096218868205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2142031790450923250315213 803261921419096218868205)
                      ·
                        rfl

theorem cell23_1564347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 3].length) (baseStart_1564347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564347 prefixEnd_1564347 := by exact prefixLift 1564347
  have htrace : WordTrace (prefixWord ++ tailWord_1564347) baseStart_1564347 baseEnd_1564347 := by
    simpa [prefixWord, tailWord_1564347, baseEnd_1564347] using wordTrace_append hprefix tailTrace_1564347
  have hstable : (prefixWord ++ tailWord_1564347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564347).length < 2 ^ (prefixWord ++ tailWord_1564347).sum := by decide
  have hdescent : baseEnd_1564347 < baseStart_1564347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564354 : List Nat := [3, 5, 1, 2, 12]
def baseStart_1564354 : Nat := 118140960795 + 1564354 * 2 ^ 59
def prefixEnd_1564354 : Nat := 4983230072969 + 3 ^ 40 * 1564354 * 2
def baseEnd_1564354 : Nat := 1101873135505730715337

theorem tailTrace_1564354 : CollatzResearch.WordTrace tailWord_1564354 prefixEnd_1564354 1101873135505730715337 := by
  unfold tailWord_1564354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264169443655025809447029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38037785183080068825192077 14264169443655025809447029)
  ·
    refine ⟨1337265885342658669635659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14264169443655025809447029 1337265885342658669635659)
    ·
      refine ⟨2005898828013988004453489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337265885342658669635659 2005898828013988004453489)
      ·
        refine ⟨1504424121010491003340117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2005898828013988004453489 1504424121010491003340117)
        ·
          refine ⟨1101873135505730715337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1504424121010491003340117 1101873135505730715337)
          ·
            rfl

theorem cell23_1564354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 12].length) (baseStart_1564354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564354 prefixEnd_1564354 := by exact prefixLift 1564354
  have htrace : WordTrace (prefixWord ++ tailWord_1564354) baseStart_1564354 baseEnd_1564354 := by
    simpa [prefixWord, tailWord_1564354, baseEnd_1564354] using wordTrace_append hprefix tailTrace_1564354
  have hstable : (prefixWord ++ tailWord_1564354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564354).length < 2 ^ (prefixWord ++ tailWord_1564354).sum := by decide
  have hdescent : baseEnd_1564354 < baseStart_1564354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564358 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1564358 : Nat := 118140960795 + 1564358 * 2 ^ 59
def prefixEnd_1564358 : Nat := 4983230072969 + 3 ^ 40 * 1564358 * 2
def baseEnd_1564358 : Nat := 267755856568765225276885

theorem tailTrace_1564358 : CollatzResearch.WordTrace tailWord_1564358 prefixEnd_1564358 267755856568765225276885 := by
  unfold tailWord_1564358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783025739581425372529179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38037882444403741280622485 1783025739581425372529179)
  ·
    refine ⟨2674538609372138058793769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1783025739581425372529179 2674538609372138058793769)
    ·
      refine ⟨2005903957029103544095327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2674538609372138058793769 2005903957029103544095327)
      ·
        refine ⟨3008855935543655316142991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005903957029103544095327 3008855935543655316142991)
        ·
          refine ⟨4513283903315482974214487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008855935543655316142991 4513283903315482974214487)
          ·
            refine ⟨6769925854973224461321731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513283903315482974214487 6769925854973224461321731)
            ·
              refine ⟨10154888782459836691982597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769925854973224461321731 10154888782459836691982597)
              ·
                refine ⟨1904041646711219379746737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10154888782459836691982597 1904041646711219379746737)
                ·
                  refine ⟨1428031235033414534810053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904041646711219379746737 1428031235033414534810053)
                  ·
                    refine ⟨267755856568765225276885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428031235033414534810053 267755856568765225276885)
                    ·
                      rfl

theorem cell23_1564358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1564358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564358 prefixEnd_1564358 := by exact prefixLift 1564358
  have htrace : WordTrace (prefixWord ++ tailWord_1564358) baseStart_1564358 baseEnd_1564358 := by
    simpa [prefixWord, tailWord_1564358, baseEnd_1564358] using wordTrace_append hprefix tailTrace_1564358
  have hstable : (prefixWord ++ tailWord_1564358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564358).length < 2 ^ (prefixWord ++ tailWord_1564358).sum := by decide
  have hdescent : baseEnd_1564358 < baseStart_1564358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564410 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_1564410 : Nat := 118140960795 + 1564410 * 2 ^ 59
def prefixEnd_1564410 : Nat := 4983230072969 + 3 ^ 40 * 1564410 * 2
def baseEnd_1564410 : Nat := 89254918966703274708935

theorem tailTrace_1564410 : CollatzResearch.WordTrace tailWord_1564410 prefixEnd_1564410 89254918966703274708935 := by
  unfold tailWord_1564410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264680065604306200456671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38039146841611483201217789 14264680065604306200456671)
  ·
    refine ⟨21397020098406459300685007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14264680065604306200456671 21397020098406459300685007)
    ·
      refine ⟨32095530147609688951027511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397020098406459300685007 32095530147609688951027511)
      ·
        refine ⟨48143295221414533426541267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32095530147609688951027511 48143295221414533426541267)
        ·
          refine ⟨72214942832121800139811901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48143295221414533426541267 72214942832121800139811901)
          ·
            refine ⟨27080603562045675052429463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72214942832121800139811901 27080603562045675052429463)
            ·
              refine ⟨40620905343068512578644195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27080603562045675052429463 40620905343068512578644195)
              ·
                refine ⟨60931358014602768867966293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40620905343068512578644195 60931358014602768867966293)
                ·
                  refine ⟨89254918966703274708935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 60931358014602768867966293 89254918966703274708935)
                  ·
                    rfl

theorem cell23_1564410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_1564410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564410 prefixEnd_1564410 := by exact prefixLift 1564410
  have htrace : WordTrace (prefixWord ++ tailWord_1564410) baseStart_1564410 baseEnd_1564410 := by
    simpa [prefixWord, tailWord_1564410, baseEnd_1564410] using wordTrace_append hprefix tailTrace_1564410
  have hstable : (prefixWord ++ tailWord_1564410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564410).length < 2 ^ (prefixWord ++ tailWord_1564410).sum := by decide
  have hdescent : baseEnd_1564410 < baseStart_1564410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564417 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1564417 : Nat := 118140960795 + 1564417 * 2 ^ 59
def prefixEnd_1564417 : Nat := 4983230072969 + 3 ^ 40 * 1564417 * 2
def baseEnd_1564417 : Nat := 803297865064910944992883

theorem tailTrace_1564417 : CollatzResearch.WordTrace tailWord_1564417 prefixEnd_1564417 803297865064910944992883 := by
  unfold tailWord_1564417
  simp only [CollatzResearch.WordTrace]
  refine ⟨57058975573391864997331505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38039317048927909998221003 57058975573391864997331505)
  ·
    refine ⟨42794231680043898747998629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57058975573391864997331505 42794231680043898747998629)
    ·
      refine ⟨8023918440008231015249743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42794231680043898747998629 8023918440008231015249743)
      ·
        refine ⟨12035877660012346522874615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023918440008231015249743 12035877660012346522874615)
        ·
          refine ⟨18053816490018519784311923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12035877660012346522874615 18053816490018519784311923)
          ·
            refine ⟨27080724735027779676467885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18053816490018519784311923 27080724735027779676467885)
            ·
              refine ⟨10155271775635417378675457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27080724735027779676467885 10155271775635417378675457)
              ·
                refine ⟨7616453831726563034006593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10155271775635417378675457 7616453831726563034006593)
                ·
                  refine ⟨5712340373794922275504945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7616453831726563034006593 5712340373794922275504945)
                  ·
                    refine ⟨4284255280346191706628709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5712340373794922275504945 4284255280346191706628709)
                    ·
                      refine ⟨803297865064910944992883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4284255280346191706628709 803297865064910944992883)
                      ·
                        rfl

theorem cell23_1564417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1564417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564417 prefixEnd_1564417 := by exact prefixLift 1564417
  have htrace : WordTrace (prefixWord ++ tailWord_1564417) baseStart_1564417 baseEnd_1564417 := by
    simpa [prefixWord, tailWord_1564417, baseEnd_1564417] using wordTrace_append hprefix tailTrace_1564417
  have hstable : (prefixWord ++ tailWord_1564417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564417).length < 2 ^ (prefixWord ++ tailWord_1564417).sum := by decide
  have hdescent : baseEnd_1564417 < baseStart_1564417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564474 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_1564474 : Nat := 118140960795 + 1564474 * 2 ^ 59
def prefixEnd_1564474 : Nat := 4983230072969 + 3 ^ 40 * 1564474 * 2
def baseEnd_1564474 : Nat := 267775711154072407326707

theorem tailTrace_1564474 : CollatzResearch.WordTrace tailWord_1564474 prefixEnd_1564474 267775711154072407326707 := by
  unfold tailWord_1564474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14265263633546340933039119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38040703022790242488104317 14265263633546340933039119)
  ·
    refine ⟨21397895450319511399558679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14265263633546340933039119 21397895450319511399558679)
    ·
      refine ⟨32096843175479267099338019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397895450319511399558679 32096843175479267099338019)
      ·
        refine ⟨48145264763218900649007029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32096843175479267099338019 48145264763218900649007029)
        ·
          refine ⟨4513618571551771935844409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48145264763218900649007029 4513618571551771935844409)
          ·
            refine ⟨3385213928663828951883307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4513618571551771935844409 3385213928663828951883307)
            ·
              refine ⟨5077820892995743427824961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385213928663828951883307 5077820892995743427824961)
              ·
                refine ⟨3808365669746807570868721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077820892995743427824961 3808365669746807570868721)
                ·
                  refine ⟨2856274252310105678151541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3808365669746807570868721 2856274252310105678151541)
                  ·
                    refine ⟨267775711154072407326707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2856274252310105678151541 267775711154072407326707)
                    ·
                      rfl

theorem cell23_1564474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_1564474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564474 prefixEnd_1564474 := by exact prefixLift 1564474
  have htrace : WordTrace (prefixWord ++ tailWord_1564474) baseStart_1564474 baseEnd_1564474 := by
    simpa [prefixWord, tailWord_1564474, baseEnd_1564474] using wordTrace_append hprefix tailTrace_1564474
  have hstable : (prefixWord ++ tailWord_1564474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564474).length < 2 ^ (prefixWord ++ tailWord_1564474).sum := by decide
  have hdescent : baseEnd_1564474 < baseStart_1564474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564478 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_1564478 : Nat := 118140960795 + 1564478 * 2 ^ 59
def prefixEnd_1564478 : Nat := 4983230072969 + 3 ^ 40 * 1564478 * 2
def baseEnd_1564478 : Nat := 89258798598315022925567

theorem tailTrace_1564478 : CollatzResearch.WordTrace tailWord_1564478 prefixEnd_1564478 89258798598315022925567 := by
  unfold tailWord_1564478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7132650053271359051912761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38040800284113914943534725 7132650053271359051912761)
  ·
    refine ⟨5349487539953519288934571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7132650053271359051912761 5349487539953519288934571)
    ·
      refine ⟨8024231309930278933401857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5349487539953519288934571 8024231309930278933401857)
      ·
        refine ⟨6018173482447709200051393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8024231309930278933401857 6018173482447709200051393)
        ·
          refine ⟨4513630111835781900038545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6018173482447709200051393 4513630111835781900038545)
          ·
            refine ⟨3385222583876836425028909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4513630111835781900038545 3385222583876836425028909)
            ·
              refine ⟨1269458468953813659385841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385222583876836425028909 1269458468953813659385841)
              ·
                refine ⟨952093851715360244539381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269458468953813659385841 952093851715360244539381)
                ·
                  refine ⟨89258798598315022925567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952093851715360244539381 89258798598315022925567)
                  ·
                    rfl

theorem cell23_1564478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_1564478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564478 prefixEnd_1564478 := by exact prefixLift 1564478
  have htrace : WordTrace (prefixWord ++ tailWord_1564478) baseStart_1564478 baseEnd_1564478 := by
    simpa [prefixWord, tailWord_1564478, baseEnd_1564478] using wordTrace_append hprefix tailTrace_1564478
  have hstable : (prefixWord ++ tailWord_1564478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564478).length < 2 ^ (prefixWord ++ tailWord_1564478).sum := by decide
  have hdescent : baseEnd_1564478 < baseStart_1564478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564537 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1564537 : Nat := 118140960795 + 1564537 * 2 ^ 59
def prefixEnd_1564537 : Nat := 4983230072969 + 3 ^ 40 * 1564537 * 2
def baseEnd_1564537 : Nat := 803359482743450475492331

theorem tailTrace_1564537 : CollatzResearch.WordTrace tailWord_1564537 prefixEnd_1564537 803359482743450475492331 := by
  unfold tailWord_1564537
  simp only [CollatzResearch.WordTrace]
  refine ⟨57063352332957125491699865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38042234888638083661133243 57063352332957125491699865)
  ·
    refine ⟨42797514249717844118774899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57063352332957125491699865 42797514249717844118774899)
    ·
      refine ⟨64196271374576766178162349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42797514249717844118774899 64196271374576766178162349)
      ·
        refine ⟨24073601765466287316810881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64196271374576766178162349 24073601765466287316810881)
        ·
          refine ⟨18055201324099715487608161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24073601765466287316810881 18055201324099715487608161)
          ·
            refine ⟨13541400993074786615706121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18055201324099715487608161 13541400993074786615706121)
            ·
              refine ⟨10156050744806089961779591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13541400993074786615706121 10156050744806089961779591)
              ·
                refine ⟨15234076117209134942669387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10156050744806089961779591 15234076117209134942669387)
                ·
                  refine ⟨22851114175813702414004081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15234076117209134942669387 22851114175813702414004081)
                  ·
                    refine ⟨17138335631860276810503061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22851114175813702414004081 17138335631860276810503061)
                    ·
                      refine ⟨803359482743450475492331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17138335631860276810503061 803359482743450475492331)
                      ·
                        rfl

theorem cell23_1564537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1564537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564537 prefixEnd_1564537 := by exact prefixLift 1564537
  have htrace : WordTrace (prefixWord ++ tailWord_1564537) baseStart_1564537 baseEnd_1564537 := by
    simpa [prefixWord, tailWord_1564537, baseEnd_1564537] using wordTrace_append hprefix tailTrace_1564537
  have hstable : (prefixWord ++ tailWord_1564537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564537).length < 2 ^ (prefixWord ++ tailWord_1564537).sum := by decide
  have hdescent : baseEnd_1564537 < baseStart_1564537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564538 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_1564538 : Nat := 118140960795 + 1564538 * 2 ^ 59
def prefixEnd_1564538 : Nat := 4983230072969 + 3 ^ 40 * 1564538 * 2
def baseEnd_1564538 : Nat := 267786665408034990526609

theorem tailTrace_1564538 : CollatzResearch.WordTrace tailWord_1564538 prefixEnd_1564538 267786665408034990526609 := by
  unfold tailWord_1564538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14265847201488375665621567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38042259203969001774990845 14265847201488375665621567)
  ·
    refine ⟨21398770802232563498432351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14265847201488375665621567 21398770802232563498432351)
    ·
      refine ⟨32098156203348845247648527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21398770802232563498432351 32098156203348845247648527)
      ·
        refine ⟨48147234305023267871472791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32098156203348845247648527 48147234305023267871472791)
        ·
          refine ⟨72220851457534901807209187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48147234305023267871472791 72220851457534901807209187)
          ·
            refine ⟨108331277186302352710813781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72220851457534901807209187 108331277186302352710813781)
            ·
              refine ⟨1269507154526980695829849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 108331277186302352710813781 1269507154526980695829849)
              ·
                refine ⟨952130365895235521872387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269507154526980695829849 952130365895235521872387)
                ·
                  refine ⟨1428195548842853282808581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952130365895235521872387 1428195548842853282808581)
                  ·
                    refine ⟨267786665408034990526609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428195548842853282808581 267786665408034990526609)
                    ·
                      rfl

theorem cell23_1564538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_1564538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564538 prefixEnd_1564538 := by exact prefixLift 1564538
  have htrace : WordTrace (prefixWord ++ tailWord_1564538) baseStart_1564538 baseEnd_1564538 := by
    simpa [prefixWord, tailWord_1564538, baseEnd_1564538] using wordTrace_append hprefix tailTrace_1564538
  have hstable : (prefixWord ++ tailWord_1564538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564538).length < 2 ^ (prefixWord ++ tailWord_1564538).sum := by decide
  have hdescent : baseEnd_1564538 < baseStart_1564538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564607 : List Nat := [1, 1, 2, 2, 2, 1, 4, 10]
def baseStart_1564607 : Nat := 118140960795 + 1564607 * 2 ^ 59
def prefixEnd_1564607 : Nat := 4983230072969 + 3 ^ 40 * 1564607 * 2
def baseEnd_1564607 : Nat := 29755386162565377837667

theorem tailTrace_1564607 : CollatzResearch.WordTrace tailWord_1564607 prefixEnd_1564607 29755386162565377837667 := by
  unfold tailWord_1564607
  simp only [CollatzResearch.WordTrace]
  refine ⟨57065905442703527446748075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38043936961802351631165383 57065905442703527446748075)
  ·
    refine ⟨85598858164055291170122113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57065905442703527446748075 85598858164055291170122113)
    ·
      refine ⟨64199143623041468377591585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85598858164055291170122113 64199143623041468377591585)
      ·
        refine ⟨48149357717281101283193689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64199143623041468377591585 48149357717281101283193689)
        ·
          refine ⟨36112018287960825962395267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48149357717281101283193689 36112018287960825962395267)
          ·
            refine ⟨54168027431941238943592901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36112018287960825962395267 54168027431941238943592901)
            ·
              refine ⟨10156505143488982301923669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54168027431941238943592901 10156505143488982301923669)
              ·
                refine ⟨29755386162565377837667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10156505143488982301923669 29755386162565377837667)
                ·
                  rfl

theorem cell23_1564607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 10].length) (baseStart_1564607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564607 prefixEnd_1564607 := by exact prefixLift 1564607
  have htrace : WordTrace (prefixWord ++ tailWord_1564607) baseStart_1564607 baseEnd_1564607 := by
    simpa [prefixWord, tailWord_1564607, baseEnd_1564607] using wordTrace_append hprefix tailTrace_1564607
  have hstable : (prefixWord ++ tailWord_1564607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564607).length < 2 ^ (prefixWord ++ tailWord_1564607).sum := by decide
  have hdescent : baseEnd_1564607 < baseStart_1564607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564617 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_1564617 : Nat := 118140960795 + 1564617 * 2 ^ 59
def prefixEnd_1564617 : Nat := 4983230072969 + 3 ^ 40 * 1564617 * 2
def baseEnd_1564617 : Nat := 803400561195810162491963

theorem tailTrace_1564617 : CollatzResearch.WordTrace tailWord_1564617 prefixEnd_1564617 803400561195810162491963 := by
  unfold tailWord_1564617
  simp only [CollatzResearch.WordTrace]
  refine ⟨57066270172667299154612105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38044180115111532769741403 57066270172667299154612105)
  ·
    refine ⟨42799702629500474365959079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57066270172667299154612105 42799702629500474365959079)
    ·
      refine ⟨64199553944250711548938619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42799702629500474365959079 64199553944250711548938619)
      ·
        refine ⟨96299330916376067323407929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64199553944250711548938619 96299330916376067323407929)
        ·
          refine ⟨72224498187282050492555947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96299330916376067323407929 72224498187282050492555947)
          ·
            refine ⟨108336747280923075738833921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72224498187282050492555947 108336747280923075738833921)
            ·
              refine ⟨81252560460692306804125441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108336747280923075738833921 81252560460692306804125441)
              ·
                refine ⟨60939420345519230103094081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81252560460692306804125441 60939420345519230103094081)
                ·
                  refine ⟨45704565259139422577320561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60939420345519230103094081 45704565259139422577320561)
                  ·
                    refine ⟨34278423944354566932990421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45704565259139422577320561 34278423944354566932990421)
                    ·
                      refine ⟨803400561195810162491963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34278423944354566932990421 803400561195810162491963)
                      ·
                        rfl

theorem cell23_1564617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_1564617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564617 prefixEnd_1564617 := by exact prefixLift 1564617
  have htrace : WordTrace (prefixWord ++ tailWord_1564617) baseStart_1564617 baseEnd_1564617 := by
    simpa [prefixWord, tailWord_1564617, baseEnd_1564617] using wordTrace_append hprefix tailTrace_1564617
  have hstable : (prefixWord ++ tailWord_1564617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564617).length < 2 ^ (prefixWord ++ tailWord_1564617).sum := by decide
  have hdescent : baseEnd_1564617 < baseStart_1564617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564618 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_1564618 : Nat := 118140960795 + 1564618 * 2 ^ 59
def prefixEnd_1564618 : Nat := 4983230072969 + 3 ^ 40 * 1564618 * 2
def baseEnd_1564618 : Nat := 803401074676464658579459

theorem tailTrace_1564618 : CollatzResearch.WordTrace tailWord_1564618 prefixEnd_1564618 803401074676464658579459 := by
  unfold tailWord_1564618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266576661415919081349627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38044204430442450883599005 14266576661415919081349627)
  ·
    refine ⟨21399864992123878622024441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14266576661415919081349627 21399864992123878622024441)
    ·
      refine ⟨16049898744092908966518331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21399864992123878622024441 16049898744092908966518331)
      ·
        refine ⟨24074848116139363449777497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16049898744092908966518331 24074848116139363449777497)
        ·
          refine ⟨18056136087104522587333123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24074848116139363449777497 18056136087104522587333123)
          ·
            refine ⟨27084204130656783880999685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18056136087104522587333123 27084204130656783880999685)
            ·
              refine ⟨5078288274498146977687441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27084204130656783880999685 5078288274498146977687441)
              ·
                refine ⟨3808716205873610233265581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5078288274498146977687441 3808716205873610233265581)
                ·
                  refine ⟨1428268577202603837474593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3808716205873610233265581 1428268577202603837474593)
                  ·
                    refine ⟨1071201432901952878105945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428268577202603837474593 1071201432901952878105945)
                    ·
                      refine ⟨803401074676464658579459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071201432901952878105945 803401074676464658579459)
                      ·
                        rfl

theorem cell23_1564618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_1564618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564618 prefixEnd_1564618 := by exact prefixLift 1564618
  have htrace : WordTrace (prefixWord ++ tailWord_1564618) baseStart_1564618 baseEnd_1564618 := by
    simpa [prefixWord, tailWord_1564618, baseEnd_1564618] using wordTrace_append hprefix tailTrace_1564618
  have hstable : (prefixWord ++ tailWord_1564618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564618).length < 2 ^ (prefixWord ++ tailWord_1564618).sum := by decide
  have hdescent : baseEnd_1564618 < baseStart_1564618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564624 : List Nat := [2, 1, 1, 1, 1, 2, 8, 7]
def baseStart_1564624 : Nat := 118140960795 + 1564624 * 2 ^ 59
def prefixEnd_1564624 : Nat := 4983230072969 + 3 ^ 40 * 1564624 * 2
def baseEnd_1564624 : Nat := 29755709465199690189053

theorem tailTrace_1564624 : CollatzResearch.WordTrace tailWord_1564624 prefixEnd_1564624 29755709465199690189053 := by
  unfold tailWord_1564624
  simp only [CollatzResearch.WordTrace]
  refine ⟨28533262741820969675058463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38044350322427959566744617 28533262741820969675058463)
  ·
    refine ⟨42799894112731454512587695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28533262741820969675058463 42799894112731454512587695)
    ·
      refine ⟨64199841169097181768881543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42799894112731454512587695 64199841169097181768881543)
      ·
        refine ⟨96299761753645772653322315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64199841169097181768881543 96299761753645772653322315)
        ·
          refine ⟨144449642630468658979983473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96299761753645772653322315 144449642630468658979983473)
          ·
            refine ⟨108337231972851494234987605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144449642630468658979983473 108337231972851494234987605)
            ·
              refine ⟨1269576937181853448066261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 108337231972851494234987605 1269576937181853448066261)
              ·
                refine ⟨29755709465199690189053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1269576937181853448066261 29755709465199690189053)
                ·
                  rfl

theorem cell23_1564624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 7].length) (baseStart_1564624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564624 prefixEnd_1564624 := by exact prefixLift 1564624
  have htrace : WordTrace (prefixWord ++ tailWord_1564624) baseStart_1564624 baseEnd_1564624 := by
    simpa [prefixWord, tailWord_1564624, baseEnd_1564624] using wordTrace_append hprefix tailTrace_1564624
  have hstable : (prefixWord ++ tailWord_1564624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564624).length < 2 ^ (prefixWord ++ tailWord_1564624).sum := by decide
  have hdescent : baseEnd_1564624 < baseStart_1564624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564662 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1564662 : Nat := 118140960795 + 1564662 * 2 ^ 59
def prefixEnd_1564662 : Nat := 4983230072969 + 3 ^ 40 * 1564662 * 2
def baseEnd_1564662 : Nat := 267807889275087495476419

theorem tailTrace_1564662 : CollatzResearch.WordTrace tailWord_1564662 prefixEnd_1564662 267807889275087495476419 := by
  unfold tailWord_1564662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566744466094016990000015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38045274305002847893333493 3566744466094016990000015)
  ·
    refine ⟨5350116699141025485000023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3566744466094016990000015 5350116699141025485000023)
    ·
      refine ⟨8025175048711538227500035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350116699141025485000023 8025175048711538227500035)
      ·
        refine ⟨12037762573067307341250053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8025175048711538227500035 12037762573067307341250053)
        ·
          refine ⟨2257080482450120126484385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12037762573067307341250053 2257080482450120126484385)
          ·
            refine ⟨1692810361837590094863289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257080482450120126484385 1692810361837590094863289)
            ·
              refine ⟨1269607771378192571147467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692810361837590094863289 1269607771378192571147467)
              ·
                refine ⟨1904411657067288856721201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269607771378192571147467 1904411657067288856721201)
                ·
                  refine ⟨1428308742800466642540901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904411657067288856721201 1428308742800466642540901)
                  ·
                    refine ⟨267807889275087495476419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428308742800466642540901 267807889275087495476419)
                    ·
                      rfl

theorem cell23_1564662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1564662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564662 prefixEnd_1564662 := by exact prefixLift 1564662
  have htrace : WordTrace (prefixWord ++ tailWord_1564662) baseStart_1564662 baseEnd_1564662 := by
    simpa [prefixWord, tailWord_1564662, baseEnd_1564662] using wordTrace_append hprefix tailTrace_1564662
  have hstable : (prefixWord ++ tailWord_1564662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564662).length < 2 ^ (prefixWord ++ tailWord_1564662).sum := by decide
  have hdescent : baseEnd_1564662 < baseStart_1564662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564668 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_1564668 : Nat := 118140960795 + 1564668 * 2 ^ 59
def prefixEnd_1564668 : Nat := 4983230072969 + 3 ^ 40 * 1564668 * 2
def baseEnd_1564668 : Nat := 803426748709189462954229

theorem tailTrace_1564668 : CollatzResearch.WordTrace tailWord_1564668 prefixEnd_1564668 803426748709189462954229 := by
  unfold tailWord_1564668
  simp only [CollatzResearch.WordTrace]
  refine ⟨28534065147741267432359329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38045420196988356576479105 28534065147741267432359329)
  ·
    refine ⟨21400548860805950574269497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28534065147741267432359329 21400548860805950574269497)
    ·
      refine ⟨16050411645604462930702123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21400548860805950574269497 16050411645604462930702123)
      ·
        refine ⟨24075617468406694396053185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16050411645604462930702123 24075617468406694396053185)
        ·
          refine ⟨18056713101305020797039889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24075617468406694396053185 18056713101305020797039889)
          ·
            refine ⟨13542534825978765597779917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18056713101305020797039889 13542534825978765597779917)
            ·
              refine ⟨5078450559742037099167469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13542534825978765597779917 5078450559742037099167469)
              ·
                refine ⟨1904418959903263912187801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5078450559742037099167469 1904418959903263912187801)
                ·
                  refine ⟨1428314219927447934140851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904418959903263912187801 1428314219927447934140851)
                  ·
                    refine ⟨2142471329891171901211277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428314219927447934140851 2142471329891171901211277)
                    ·
                      refine ⟨803426748709189462954229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2142471329891171901211277 803426748709189462954229)
                      ·
                        rfl

theorem cell23_1564668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_1564668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564668 prefixEnd_1564668 := by exact prefixLift 1564668
  have htrace : WordTrace (prefixWord ++ tailWord_1564668) baseStart_1564668 baseEnd_1564668 := by
    simpa [prefixWord, tailWord_1564668, baseEnd_1564668] using wordTrace_append hprefix tailTrace_1564668
  have hstable : (prefixWord ++ tailWord_1564668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564668).length < 2 ^ (prefixWord ++ tailWord_1564668).sum := by decide
  have hdescent : baseEnd_1564668 < baseStart_1564668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564691 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 3, 4, 2]
def baseStart_1564691 : Nat := 118140960795 + 1564691 * 2 ^ 59
def prefixEnd_1564691 : Nat := 4983230072969 + 3 ^ 40 * 1564691 * 2
def baseEnd_1564691 : Nat := 803438558764242872966623

theorem tailTrace_1564691 : CollatzResearch.WordTrace tailWord_1564691 prefixEnd_1564691 803438558764242872966623 := by
  unfold tailWord_1564691
  simp only [CollatzResearch.WordTrace]
  refine ⟨57068969174399209792805927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38045979449599473195203951 57068969174399209792805927)
  ·
    refine ⟨85603453761598814689208891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57068969174399209792805927 85603453761598814689208891)
    ·
      refine ⟨128405180642398222033813337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85603453761598814689208891 128405180642398222033813337)
      ·
        refine ⟨96303885481798666525360003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128405180642398222033813337 96303885481798666525360003)
        ·
          refine ⟨144455828222697999788040005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96303885481798666525360003 144455828222697999788040005)
          ·
            refine ⟨27085467791755874960257501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144455828222697999788040005 27085467791755874960257501)
            ·
              refine ⟨10157050421908453110096563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27085467791755874960257501 10157050421908453110096563)
              ·
                refine ⟨15235575632862679665144845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10157050421908453110096563 15235575632862679665144845)
                ·
                  refine ⟨5713340862323504874429317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15235575632862679665144845 5713340862323504874429317)
                  ·
                    refine ⟨1071251411685657163955497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713340862323504874429317 1071251411685657163955497)
                    ·
                      refine ⟨803438558764242872966623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071251411685657163955497 803438558764242872966623)
                      ·
                        rfl

theorem cell23_1564691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4, 2].length) (baseStart_1564691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564691 prefixEnd_1564691 := by exact prefixLift 1564691
  have htrace : WordTrace (prefixWord ++ tailWord_1564691) baseStart_1564691 baseEnd_1564691 := by
    simpa [prefixWord, tailWord_1564691, baseEnd_1564691] using wordTrace_append hprefix tailTrace_1564691
  have hstable : (prefixWord ++ tailWord_1564691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564691).length < 2 ^ (prefixWord ++ tailWord_1564691).sum := by decide
  have hdescent : baseEnd_1564691 < baseStart_1564691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564721 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1564721 : Nat := 118140960795 + 1564721 * 2 ^ 59
def prefixEnd_1564721 : Nat := 4983230072969 + 3 ^ 40 * 1564721 * 2
def baseEnd_1564721 : Nat := 803453963183877755591485

theorem tailTrace_1564721 : CollatzResearch.WordTrace tailWord_1564721 prefixEnd_1564721 803453963183877755591485 := by
  unfold tailWord_1564721
  simp only [CollatzResearch.WordTrace]
  refine ⟨57070063364290524916398017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38046708909527016610932011 57070063364290524916398017)
  ·
    refine ⟨42802547523217893687298513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57070063364290524916398017 42802547523217893687298513)
    ·
      refine ⟨32101910642413420265473885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42802547523217893687298513 32101910642413420265473885)
      ·
        refine ⟨12038216490905032599552707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32101910642413420265473885 12038216490905032599552707)
        ·
          refine ⟨18057324736357548899329061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12038216490905032599552707 18057324736357548899329061)
          ·
            refine ⟨3385748388067040418624199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18057324736357548899329061 3385748388067040418624199)
            ·
              refine ⟨5078622582100560627936299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385748388067040418624199 5078622582100560627936299)
              ·
                refine ⟨7617933873150840941904449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078622582100560627936299 7617933873150840941904449)
                ·
                  refine ⟨5713450404863130706428337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7617933873150840941904449 5713450404863130706428337)
                  ·
                    refine ⟨4285087803647348029821253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5713450404863130706428337 4285087803647348029821253)
                    ·
                      refine ⟨803453963183877755591485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4285087803647348029821253 803453963183877755591485)
                      ·
                        rfl

theorem cell23_1564721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1564721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564721 prefixEnd_1564721 := by exact prefixLift 1564721
  have htrace : WordTrace (prefixWord ++ tailWord_1564721) baseStart_1564721 baseEnd_1564721 := by
    simpa [prefixWord, tailWord_1564721, baseEnd_1564721] using wordTrace_append hprefix tailTrace_1564721
  have hstable : (prefixWord ++ tailWord_1564721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564721).length < 2 ^ (prefixWord ++ tailWord_1564721).sum := by decide
  have hdescent : baseEnd_1564721 < baseStart_1564721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564725 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_1564725 : Nat := 118140960795 + 1564725 * 2 ^ 59
def prefixEnd_1564725 : Nat := 4983230072969 + 3 ^ 40 * 1564725 * 2
def baseEnd_1564725 : Nat := 803456017106495739941467

theorem tailTrace_1564725 : CollatzResearch.WordTrace tailWord_1564725 prefixEnd_1564725 803456017106495739941467 := by
  unfold tailWord_1564725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57070209256276033599543629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38046806170850689066362419 57070209256276033599543629)
  ·
    refine ⟨21401328471103512599828861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57070209256276033599543629 21401328471103512599828861)
    ·
      refine ⟨8025498176663817224935823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21401328471103512599828861 8025498176663817224935823)
      ·
        refine ⟨12038247264995725837403735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8025498176663817224935823 12038247264995725837403735)
        ·
          refine ⟨18057370897493588756105603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12038247264995725837403735 18057370897493588756105603)
          ·
            refine ⟨27086056346240383134158405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18057370897493588756105603 27086056346240383134158405)
            ·
              refine ⟨5078635564920071837654701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27086056346240383134158405 5078635564920071837654701)
              ·
                refine ⟨1904488336845026939120513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5078635564920071837654701 1904488336845026939120513)
                ·
                  refine ⟨1428366252633770204340385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904488336845026939120513 1428366252633770204340385)
                  ·
                    refine ⟨1071274689475327653255289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428366252633770204340385 1071274689475327653255289)
                    ·
                      refine ⟨803456017106495739941467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071274689475327653255289 803456017106495739941467)
                      ·
                        rfl

theorem cell23_1564725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_1564725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564725 prefixEnd_1564725 := by exact prefixLift 1564725
  have htrace : WordTrace (prefixWord ++ tailWord_1564725) baseStart_1564725 baseEnd_1564725 := by
    simpa [prefixWord, tailWord_1564725, baseEnd_1564725] using wordTrace_append hprefix tailTrace_1564725
  have hstable : (prefixWord ++ tailWord_1564725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564725).length < 2 ^ (prefixWord ++ tailWord_1564725).sum := by decide
  have hdescent : baseEnd_1564725 < baseStart_1564725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564742 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1564742 : Nat := 118140960795 + 1564742 * 2 ^ 59
def prefixEnd_1564742 : Nat := 4983230072969 + 3 ^ 40 * 1564742 * 2
def baseEnd_1564742 : Nat := 803464746277622173428889

theorem tailTrace_1564742 : CollatzResearch.WordTrace tailWord_1564742 prefixEnd_1564742 803464746277622173428889 := by
  unfold tailWord_1564742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783463415537951421966015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38047219531476297001941653 1783463415537951421966015)
  ·
    refine ⟨2675195123306927132949023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1783463415537951421966015 2675195123306927132949023)
    ·
      refine ⟨4012792684960390699423535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2675195123306927132949023 4012792684960390699423535)
      ·
        refine ⟨6019189027440586049135303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012792684960390699423535 6019189027440586049135303)
        ·
          refine ⟨9028783541160879073702955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019189027440586049135303 9028783541160879073702955)
          ·
            refine ⟨13543175311741318610554433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028783541160879073702955 13543175311741318610554433)
            ·
              refine ⟨10157381483805988957915825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13543175311741318610554433 10157381483805988957915825)
              ·
                refine ⟨7618036112854491718436869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10157381483805988957915825 7618036112854491718436869)
                ·
                  refine ⟨1428381771160217197206913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7618036112854491718436869 1428381771160217197206913)
                  ·
                    refine ⟨1071286328370162897905185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428381771160217197206913 1071286328370162897905185)
                    ·
                      refine ⟨803464746277622173428889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071286328370162897905185 803464746277622173428889)
                      ·
                        rfl

theorem cell23_1564742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1564742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564742 prefixEnd_1564742 := by exact prefixLift 1564742
  have htrace : WordTrace (prefixWord ++ tailWord_1564742) baseStart_1564742 baseEnd_1564742 := by
    simpa [prefixWord, tailWord_1564742, baseEnd_1564742] using wordTrace_append hprefix tailTrace_1564742
  have hstable : (prefixWord ++ tailWord_1564742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564742).length < 2 ^ (prefixWord ++ tailWord_1564742).sum := by decide
  have hdescent : baseEnd_1564742 < baseStart_1564742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564751 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 4, 5, 2]
def baseStart_1564751 : Nat := 118140960795 + 1564751 * 2 ^ 59
def prefixEnd_1564751 : Nat := 4983230072969 + 3 ^ 40 * 1564751 * 2
def baseEnd_1564751 : Nat := 803469367603512638216347

theorem tailTrace_1564751 : CollatzResearch.WordTrace tailWord_1564751 prefixEnd_1564751 803469367603512638216347 := by
  unfold tailWord_1564751
  simp only [CollatzResearch.WordTrace]
  refine ⟨57071157554181840039990107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38047438369454560026660071 57071157554181840039990107)
  ·
    refine ⟨85606736331272760059985161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57071157554181840039990107 85606736331272760059985161)
    ·
      refine ⟨64205052248454570044988871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85606736331272760059985161 64205052248454570044988871)
      ·
        refine ⟨96307578372681855067483307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64205052248454570044988871 96307578372681855067483307)
        ·
          refine ⟨144461367559022782601224961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96307578372681855067483307 144461367559022782601224961)
          ·
            refine ⟨108346025669267086950918721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144461367559022782601224961 108346025669267086950918721)
            ·
              refine ⟨81259519251950315213189041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108346025669267086950918721 81259519251950315213189041)
              ·
                refine ⟨60944639438962736409891781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81259519251950315213189041 60944639438962736409891781)
                ·
                  refine ⟨11427119894805513076854709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60944639438962736409891781 11427119894805513076854709)
                  ·
                    refine ⟨1071292490138016850955129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11427119894805513076854709 1071292490138016850955129)
                    ·
                      refine ⟨803469367603512638216347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071292490138016850955129 803469367603512638216347)
                      ·
                        rfl

theorem cell23_1564751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5, 2].length) (baseStart_1564751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564751 prefixEnd_1564751 := by exact prefixLift 1564751
  have htrace : WordTrace (prefixWord ++ tailWord_1564751) baseStart_1564751 baseEnd_1564751 := by
    simpa [prefixWord, tailWord_1564751, baseEnd_1564751] using wordTrace_append hprefix tailTrace_1564751
  have hstable : (prefixWord ++ tailWord_1564751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564751).length < 2 ^ (prefixWord ++ tailWord_1564751).sum := by decide
  have hdescent : baseEnd_1564751 < baseStart_1564751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564765 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 5]
def baseStart_1564765 : Nat := 118140960795 + 1564765 * 2 ^ 59
def prefixEnd_1564765 : Nat := 4983230072969 + 3 ^ 40 * 1564765 * 2
def baseEnd_1564765 : Nat := 89275172925852842604587

theorem tailTrace_1564765 : CollatzResearch.WordTrace tailWord_1564765 prefixEnd_1564765 89275172925852842604587 := by
  unfold tailWord_1564765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57071668176131120430999749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38047778784087413620666499 57071668176131120430999749)
  ·
    refine ⟨10700937783024585080812453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57071668176131120430999749 10700937783024585080812453)
    ·
      refine ⟨2006425834317109702652335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10700937783024585080812453 2006425834317109702652335)
      ·
        refine ⟨3009638751475664553978503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006425834317109702652335 3009638751475664553978503)
        ·
          refine ⟨4514458127213496830967755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009638751475664553978503 4514458127213496830967755)
          ·
            refine ⟨6771687190820245246451633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514458127213496830967755 6771687190820245246451633)
            ·
              refine ⟨5078765393115183934838725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6771687190820245246451633 5078765393115183934838725)
              ·
                refine ⟨952268511209096987782261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5078765393115183934838725 952268511209096987782261)
                ·
                  refine ⟨89275172925852842604587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952268511209096987782261 89275172925852842604587)
                  ·
                    rfl

theorem cell23_1564765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_1564765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564765 prefixEnd_1564765 := by exact prefixLift 1564765
  have htrace : WordTrace (prefixWord ++ tailWord_1564765) baseStart_1564765 baseEnd_1564765 := by
    simpa [prefixWord, tailWord_1564765, baseEnd_1564765] using wordTrace_append hprefix tailTrace_1564765
  have hstable : (prefixWord ++ tailWord_1564765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564765).length < 2 ^ (prefixWord ++ tailWord_1564765).sum := by decide
  have hdescent : baseEnd_1564765 < baseStart_1564765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564781 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1564781 : Nat := 118140960795 + 1564781 * 2 ^ 59
def prefixEnd_1564781 : Nat := 4983230072969 + 3 ^ 40 * 1564781 * 2
def baseEnd_1564781 : Nat := 803484772023147520841209

theorem tailTrace_1564781 : CollatzResearch.WordTrace tailWord_1564781 prefixEnd_1564781 803484772023147520841209 := by
  unfold tailWord_1564781
  simp only [CollatzResearch.WordTrace]
  refine ⟨57072251744073155163582197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38048167829382103442388131 57072251744073155163582197)
  ·
    refine ⟨5350523601006858296585831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57072251744073155163582197 5350523601006858296585831)
    ·
      refine ⟨8025785401510287444878747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350523601006858296585831 8025785401510287444878747)
      ·
        refine ⟨12038678102265431167318121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8025785401510287444878747 12038678102265431167318121)
        ·
          refine ⟨9029008576699073375488591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12038678102265431167318121 9029008576699073375488591)
          ·
            refine ⟨13543512865048610063232887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029008576699073375488591 13543512865048610063232887)
            ·
              refine ⟨20315269297572915094849331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13543512865048610063232887 20315269297572915094849331)
              ·
                refine ⟨30472903946359372642273997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20315269297572915094849331 30472903946359372642273997)
                ·
                  refine ⟨11427338979884764740852749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30472903946359372642273997 11427338979884764740852749)
                  ·
                    refine ⟨4285252117456786777819781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11427338979884764740852749 4285252117456786777819781)
                    ·
                      refine ⟨803484772023147520841209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4285252117456786777819781 803484772023147520841209)
                      ·
                        rfl

theorem cell23_1564781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1564781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564781 prefixEnd_1564781 := by exact prefixLift 1564781
  have htrace : WordTrace (prefixWord ++ tailWord_1564781) baseStart_1564781 baseEnd_1564781 := by
    simpa [prefixWord, tailWord_1564781, baseEnd_1564781] using wordTrace_append hprefix tailTrace_1564781
  have hstable : (prefixWord ++ tailWord_1564781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564781).length < 2 ^ (prefixWord ++ tailWord_1564781).sum := by decide
  have hdescent : baseEnd_1564781 < baseStart_1564781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564821 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 6]
def baseStart_1564821 : Nat := 118140960795 + 1564821 * 2 ^ 59
def prefixEnd_1564821 : Nat := 4983230072969 + 3 ^ 40 * 1564821 * 2
def baseEnd_1564821 : Nat := 89278367916591929371225

theorem tailTrace_1564821 : CollatzResearch.WordTrace tailWord_1564821 prefixEnd_1564821 89278367916591929371225 := by
  unfold tailWord_1564821
  simp only [CollatzResearch.WordTrace]
  refine ⟨57073710663928241995038317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38049140442618827996692211 57073710663928241995038317)
  ·
    refine ⟨21402641498973090748139369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57073710663928241995038317 21402641498973090748139369)
    ·
      refine ⟨16051981124229818061104527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21402641498973090748139369 16051981124229818061104527)
      ·
        refine ⟨24077971686344727091656791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16051981124229818061104527 24077971686344727091656791)
        ·
          refine ⟨36116957529517090637485187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24077971686344727091656791 36116957529517090637485187)
          ·
            refine ⟨54175436294275635956227781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36116957529517090637485187 54175436294275635956227781)
            ·
              refine ⟨10157894305176681741792709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54175436294275635956227781 10157894305176681741792709)
              ·
                refine ⟨1904605182220627826586133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10157894305176681741792709 1904605182220627826586133)
                ·
                  refine ⟨89278367916591929371225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1904605182220627826586133 89278367916591929371225)
                  ·
                    rfl

theorem cell23_1564821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_1564821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564821 prefixEnd_1564821 := by exact prefixLift 1564821
  have htrace : WordTrace (prefixWord ++ tailWord_1564821) baseStart_1564821 baseEnd_1564821 := by
    simpa [prefixWord, tailWord_1564821, baseEnd_1564821] using wordTrace_append hprefix tailTrace_1564821
  have hstable : (prefixWord ++ tailWord_1564821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564821).length < 2 ^ (prefixWord ++ tailWord_1564821).sum := by decide
  have hdescent : baseEnd_1564821 < baseStart_1564821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564858 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2]
def baseStart_1564858 : Nat := 118140960795 + 1564858 * 2 ^ 59
def prefixEnd_1564858 : Nat := 4983230072969 + 3 ^ 40 * 1564858 * 2
def baseEnd_1564858 : Nat := 803524310033543719578355

theorem tailTrace_1564858 : CollatzResearch.WordTrace tailWord_1564858 prefixEnd_1564858 803524310033543719578355 := by
  unfold tailWord_1564858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268765041198549328533807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38050040109862798209423485 14268765041198549328533807)
  ·
    refine ⟨21403147561797823992800711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14268765041198549328533807 21403147561797823992800711)
    ·
      refine ⟨32104721342696735989201067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21403147561797823992800711 32104721342696735989201067)
      ·
        refine ⟨48157082014045103983801601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32104721342696735989201067 48157082014045103983801601)
        ·
          refine ⟨36117811510533827987851201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48157082014045103983801601 36117811510533827987851201)
          ·
            refine ⟨27088358632900370990888401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36117811510533827987851201 27088358632900370990888401)
            ·
              refine ⟨20316268974675278243166301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27088358632900370990888401 20316268974675278243166301)
              ·
                refine ⟨7618600865503229341187363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20316268974675278243166301 7618600865503229341187363)
                ·
                  refine ⟨11427901298254844011781045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618600865503229341187363 11427901298254844011781045)
                  ·
                    refine ⟨1071365746711391626104473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11427901298254844011781045 1071365746711391626104473)
                    ·
                      refine ⟨803524310033543719578355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071365746711391626104473 803524310033543719578355)
                      ·
                        rfl

theorem cell23_1564858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_1564858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564858 prefixEnd_1564858 := by exact prefixLift 1564858
  have htrace : WordTrace (prefixWord ++ tailWord_1564858) baseStart_1564858 baseEnd_1564858 := by
    simpa [prefixWord, tailWord_1564858, baseEnd_1564858] using wordTrace_append hprefix tailTrace_1564858
  have hstable : (prefixWord ++ tailWord_1564858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564858).length < 2 ^ (prefixWord ++ tailWord_1564858).sum := by decide
  have hdescent : baseEnd_1564858 < baseStart_1564858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564876 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_1564876 : Nat := 118140960795 + 1564876 * 2 ^ 59
def prefixEnd_1564876 : Nat := 4983230072969 + 3 ^ 40 * 1564876 * 2
def baseEnd_1564876 : Nat := 267844517561774883051091

theorem tailTrace_1564876 : CollatzResearch.WordTrace tailWord_1564876 prefixEnd_1564876 267844517561774883051091 := by
  unfold tailWord_1564876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537858339364493194145241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38050477785819324258860321 28537858339364493194145241)
  ·
    refine ⟨21403393754523369895608931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28537858339364493194145241 21403393754523369895608931)
    ·
      refine ⟨32105090631785054843413397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21403393754523369895608931 32105090631785054843413397)
      ·
        refine ⟨1504926123364924445785003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32105090631785054843413397 1504926123364924445785003)
        ·
          refine ⟨2257389185047386668677505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504926123364924445785003 2257389185047386668677505)
          ·
            refine ⟨1693041888785540001508129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257389185047386668677505 1693041888785540001508129)
            ·
              refine ⟨1269781416589155001131097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693041888785540001508129 1269781416589155001131097)
              ·
                refine ⟨952336062441866250848323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269781416589155001131097 952336062441866250848323)
                ·
                  refine ⟨1428504093662799376272485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952336062441866250848323 1428504093662799376272485)
                  ·
                    refine ⟨267844517561774883051091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428504093662799376272485 267844517561774883051091)
                    ·
                      rfl

theorem cell23_1564876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_1564876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564876 prefixEnd_1564876 := by exact prefixLift 1564876
  have htrace : WordTrace (prefixWord ++ tailWord_1564876) baseStart_1564876 baseEnd_1564876 := by
    simpa [prefixWord, tailWord_1564876, baseEnd_1564876] using wordTrace_append hprefix tailTrace_1564876
  have hstable : (prefixWord ++ tailWord_1564876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564876).length < 2 ^ (prefixWord ++ tailWord_1564876).sum := by decide
  have hdescent : baseEnd_1564876 < baseStart_1564876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564888 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1564888 : Nat := 118140960795 + 1564888 * 2 ^ 59
def prefixEnd_1564888 : Nat := 4983230072969 + 3 ^ 40 * 1564888 * 2
def baseEnd_1564888 : Nat := 803539714453178602203217

theorem tailTrace_1564888 : CollatzResearch.WordTrace tailWord_1564888 prefixEnd_1564888 803539714453178602203217 := by
  unfold tailWord_1564888
  simp only [CollatzResearch.WordTrace]
  refine ⟨28538077177342756218863659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38050769569790341625151545 28538077177342756218863659)
  ·
    refine ⟨42807115766014134328295489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28538077177342756218863659 42807115766014134328295489)
    ·
      refine ⟨32105336824510600746221617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42807115766014134328295489 32105336824510600746221617)
      ·
        refine ⟨24079002618382950559666213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32105336824510600746221617 24079002618382950559666213)
        ·
          refine ⟨4514812990946803229937415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24079002618382950559666213 4514812990946803229937415)
          ·
            refine ⟨6772219486420204844906123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514812990946803229937415 6772219486420204844906123)
            ·
              refine ⟨10158329229630307267359185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772219486420204844906123 10158329229630307267359185)
              ·
                refine ⟨7618746922222730450519389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10158329229630307267359185 7618746922222730450519389)
                ·
                  refine ⟨2857030095833523918944771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7618746922222730450519389 2857030095833523918944771)
                  ·
                    refine ⟨4285545143750285878417157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2857030095833523918944771 4285545143750285878417157)
                    ·
                      refine ⟨803539714453178602203217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4285545143750285878417157 803539714453178602203217)
                      ·
                        rfl

theorem cell23_1564888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1564888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564888 prefixEnd_1564888 := by exact prefixLift 1564888
  have htrace : WordTrace (prefixWord ++ tailWord_1564888) baseStart_1564888 baseEnd_1564888 := by
    simpa [prefixWord, tailWord_1564888, baseEnd_1564888] using wordTrace_append hprefix tailTrace_1564888
  have hstable : (prefixWord ++ tailWord_1564888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564888).length < 2 ^ (prefixWord ++ tailWord_1564888).sum := by decide
  have hdescent : baseEnd_1564888 < baseStart_1564888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564891 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 3]
def baseStart_1564891 : Nat := 118140960795 + 1564891 * 2 ^ 59
def prefixEnd_1564891 : Nat := 4983230072969 + 3 ^ 40 * 1564891 * 2
def baseEnd_1564891 : Nat := 803541254895142090465703

theorem tailTrace_1564891 : CollatzResearch.WordTrace tailWord_1564891 prefixEnd_1564891 803541254895142090465703 := by
  unfold tailWord_1564891
  simp only [CollatzResearch.WordTrace]
  refine ⟨57076263773674643950086527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38050842515783095966724351 57076263773674643950086527)
  ·
    refine ⟨85614395660511965925129791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57076263773674643950086527 85614395660511965925129791)
    ·
      refine ⟨128421593490767948887694687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85614395660511965925129791 128421593490767948887694687)
      ·
        refine ⟨192632390236151923331542031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128421593490767948887694687 192632390236151923331542031)
        ·
          refine ⟨288948585354227884997313047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192632390236151923331542031 288948585354227884997313047)
          ·
            refine ⟨433422878031341827495969571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288948585354227884997313047 433422878031341827495969571)
            ·
              refine ⟨650134317047012741243954357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433422878031341827495969571 650134317047012741243954357)
              ·
                refine ⟨60950092223157444491620721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 650134317047012741243954357 60950092223157444491620721)
                ·
                  refine ⟨45712569167368083368715541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60950092223157444491620721 45712569167368083368715541)
                  ·
                    refine ⟨2142776679720378907908541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45712569167368083368715541 2142776679720378907908541)
                    ·
                      refine ⟨803541254895142090465703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2142776679720378907908541 803541254895142090465703)
                      ·
                        rfl

theorem cell23_1564891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 3].length) (baseStart_1564891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564891 prefixEnd_1564891 := by exact prefixLift 1564891
  have htrace : WordTrace (prefixWord ++ tailWord_1564891) baseStart_1564891 baseEnd_1564891 := by
    simpa [prefixWord, tailWord_1564891, baseEnd_1564891] using wordTrace_append hprefix tailTrace_1564891
  have hstable : (prefixWord ++ tailWord_1564891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564891).length < 2 ^ (prefixWord ++ tailWord_1564891).sum := by decide
  have hdescent : baseEnd_1564891 < baseStart_1564891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564905 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 3, 2, 2]
def baseStart_1564905 : Nat := 118140960795 + 1564905 * 2 ^ 59
def prefixEnd_1564905 : Nat := 4983230072969 + 3 ^ 40 * 1564905 * 2
def baseEnd_1564905 : Nat := 803548443624305035690639

theorem tailTrace_1564905 : CollatzResearch.WordTrace tailWord_1564905 prefixEnd_1564905 803548443624305035690639 := by
  unfold tailWord_1564905
  simp only [CollatzResearch.WordTrace]
  refine ⟨57076774395623924341096169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38051182930415949560730779 57076774395623924341096169)
  ·
    refine ⟨42807580796717943255822127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57076774395623924341096169 42807580796717943255822127)
    ·
      refine ⟨64211371195076914883733191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42807580796717943255822127 64211371195076914883733191)
      ·
        refine ⟨96317056792615372325599787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64211371195076914883733191 96317056792615372325599787)
        ·
          refine ⟨144475585188923058488399681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96317056792615372325599787 144475585188923058488399681)
          ·
            refine ⟨108356688891692293866299761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144475585188923058488399681 108356688891692293866299761)
            ·
              refine ⟨81267516668769220399724821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108356688891692293866299761 81267516668769220399724821)
              ·
                refine ⟨3809414843848557206237101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81267516668769220399724821 3809414843848557206237101)
                ·
                  refine ⟨1428530566443208952338913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3809414843848557206237101 1428530566443208952338913)
                  ·
                    refine ⟨1071397924832406714254185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428530566443208952338913 1071397924832406714254185)
                    ·
                      refine ⟨803548443624305035690639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071397924832406714254185 803548443624305035690639)
                      ·
                        rfl

theorem cell23_1564905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 2, 2].length) (baseStart_1564905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564905 prefixEnd_1564905 := by exact prefixLift 1564905
  have htrace : WordTrace (prefixWord ++ tailWord_1564905) baseStart_1564905 baseEnd_1564905 := by
    simpa [prefixWord, tailWord_1564905, baseEnd_1564905] using wordTrace_append hprefix tailTrace_1564905
  have hstable : (prefixWord ++ tailWord_1564905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564905).length < 2 ^ (prefixWord ++ tailWord_1564905).sum := by decide
  have hdescent : baseEnd_1564905 < baseStart_1564905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564908 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_1564908 : Nat := 118140960795 + 1564908 * 2 ^ 59
def prefixEnd_1564908 : Nat := 4983230072969 + 3 ^ 40 * 1564908 * 2
def baseEnd_1564908 : Nat := 803549984066268523953125

theorem tailTrace_1564908 : CollatzResearch.WordTrace tailWord_1564908 prefixEnd_1564908 803549984066268523953125 := by
  unfold tailWord_1564908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28538441907306527926727689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38051255876408703902303585 28538441907306527926727689)
  ·
    refine ⟨21403831430479895945045767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28538441907306527926727689 21403831430479895945045767)
    ·
      refine ⟨32105747145719843917568651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21403831430479895945045767 32105747145719843917568651)
      ·
        refine ⟨48158620718579765876352977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32105747145719843917568651 48158620718579765876352977)
        ·
          refine ⟨36118965538934824407264733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48158620718579765876352977 36118965538934824407264733)
          ·
            refine ⟨13544612077100559152724275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36118965538934824407264733 13544612077100559152724275)
            ·
              refine ⟨20316918115650838729086413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13544612077100559152724275 20316918115650838729086413)
              ·
                refine ⟨7618844293369064523407405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20316918115650838729086413 7618844293369064523407405)
                ·
                  refine ⟨2857066610013399196277777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7618844293369064523407405 2857066610013399196277777)
                  ·
                    refine ⟨2142799957510049397208333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2857066610013399196277777 2142799957510049397208333)
                    ·
                      refine ⟨803549984066268523953125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2142799957510049397208333 803549984066268523953125)
                      ·
                        rfl

theorem cell23_1564908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_1564908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564908 prefixEnd_1564908 := by exact prefixLift 1564908
  have htrace : WordTrace (prefixWord ++ tailWord_1564908) baseStart_1564908 baseEnd_1564908 := by
    simpa [prefixWord, tailWord_1564908, baseEnd_1564908] using wordTrace_append hprefix tailTrace_1564908
  have hstable : (prefixWord ++ tailWord_1564908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564908).length < 2 ^ (prefixWord ++ tailWord_1564908).sum := by decide
  have hdescent : baseEnd_1564908 < baseStart_1564908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564909 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1564909 : Nat := 118140960795 + 1564909 * 2 ^ 59
def prefixEnd_1564909 : Nat := 4983230072969 + 3 ^ 40 * 1564909 * 2
def baseEnd_1564909 : Nat := 803550497546923020040621

theorem tailTrace_1564909 : CollatzResearch.WordTrace tailWord_1564909 prefixEnd_1564909 803550497546923020040621 := by
  unfold tailWord_1564909
  simp only [CollatzResearch.WordTrace]
  refine ⟨57076920287609433024241781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38051280191739622016161187 57076920287609433024241781)
  ·
    refine ⟨5350961276963384346022667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57076920287609433024241781 5350961276963384346022667)
    ·
      refine ⟨8026441915445076519034001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350961276963384346022667 8026441915445076519034001)
      ·
        refine ⟨6019831436583807389275501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8026441915445076519034001 6019831436583807389275501)
        ·
          refine ⟨2257436788718927770978313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6019831436583807389275501 2257436788718927770978313)
          ·
            refine ⟨1693077591539195828233735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257436788718927770978313 1693077591539195828233735)
            ·
              refine ⟨2539616387308793742350603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693077591539195828233735 2539616387308793742350603)
              ·
                refine ⟨3809424580963190613525905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539616387308793742350603 3809424580963190613525905)
                ·
                  refine ⟨2857068435722392960144429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3809424580963190613525905 2857068435722392960144429)
                  ·
                    refine ⟨1071400663395897360054161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2857068435722392960144429 1071400663395897360054161)
                    ·
                      refine ⟨803550497546923020040621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071400663395897360054161 803550497546923020040621)
                      ·
                        rfl

theorem cell23_1564909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1564909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564909 prefixEnd_1564909 := by exact prefixLift 1564909
  have htrace : WordTrace (prefixWord ++ tailWord_1564909) baseStart_1564909 baseEnd_1564909 := by
    simpa [prefixWord, tailWord_1564909, baseEnd_1564909] using wordTrace_append hprefix tailTrace_1564909
  have hstable : (prefixWord ++ tailWord_1564909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564909).length < 2 ^ (prefixWord ++ tailWord_1564909).sum := by decide
  have hdescent : baseEnd_1564909 < baseStart_1564909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564922 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4]
def baseStart_1564922 : Nat := 118140960795 + 1564922 * 2 ^ 59
def prefixEnd_1564922 : Nat := 4983230072969 + 3 ^ 40 * 1564922 * 2
def baseEnd_1564922 : Nat := 803557172795431469178061

theorem tailTrace_1564922 : CollatzResearch.WordTrace tailWord_1564922 prefixEnd_1564922 803557172795431469178061 := by
  unfold tailWord_1564922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269348609140584061116255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38051596291041557496310013 14269348609140584061116255)
  ·
    refine ⟨21404022913710876091674383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14269348609140584061116255 21404022913710876091674383)
    ·
      refine ⟨32106034370566314137511575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21404022913710876091674383 32106034370566314137511575)
      ·
        refine ⟨48159051555849471206267363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32106034370566314137511575 48159051555849471206267363)
        ·
          refine ⟨72238577333774206809401045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48159051555849471206267363 72238577333774206809401045)
          ·
            refine ⟨1693091656260332972095337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 72238577333774206809401045 1693091656260332972095337)
            ·
              refine ⟨1269818742195249729071503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693091656260332972095337 1269818742195249729071503)
              ·
                refine ⟨1904728113292874593607255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269818742195249729071503 1904728113292874593607255)
                ·
                  refine ⟨2857092169939311890410883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904728113292874593607255 2857092169939311890410883)
                  ·
                    refine ⟨4285638254908967835616325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2857092169939311890410883 4285638254908967835616325)
                    ·
                      refine ⟨803557172795431469178061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4285638254908967835616325 803557172795431469178061)
                      ·
                        rfl

theorem cell23_1564922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_1564922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564922 prefixEnd_1564922 := by exact prefixLift 1564922
  have htrace : WordTrace (prefixWord ++ tailWord_1564922) baseStart_1564922 baseEnd_1564922 := by
    simpa [prefixWord, tailWord_1564922, baseEnd_1564922] using wordTrace_append hprefix tailTrace_1564922
  have hstable : (prefixWord ++ tailWord_1564922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564922).length < 2 ^ (prefixWord ++ tailWord_1564922).sum := by decide
  have hdescent : baseEnd_1564922 < baseStart_1564922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564938 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1564938 : Nat := 118140960795 + 1564938 * 2 ^ 59
def prefixEnd_1564938 : Nat := 4983230072969 + 3 ^ 40 * 1564938 * 2
def baseEnd_1564938 : Nat := 803565388485903406577987

theorem tailTrace_1564938 : CollatzResearch.WordTrace tailWord_1564938 prefixEnd_1564938 803565388485903406577987 := by
  unfold tailWord_1564938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269494501126092744261867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38051985336336247318031645 14269494501126092744261867)
  ·
    refine ⟨21404241751689139116392801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14269494501126092744261867 21404241751689139116392801)
    ·
      refine ⟨16053181313766854337294601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21404241751689139116392801 16053181313766854337294601)
      ·
        refine ⟨12039885985325140752970951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16053181313766854337294601 12039885985325140752970951)
        ·
          refine ⟨18059828977987711129456427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039885985325140752970951 18059828977987711129456427)
          ·
            refine ⟨27089743466981566694184641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18059828977987711129456427 27089743466981566694184641)
            ·
              refine ⟨20317307600236175020638481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27089743466981566694184641 20317307600236175020638481)
              ·
                refine ⟨15237980700177131265478861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20317307600236175020638481 15237980700177131265478861)
                ·
                  refine ⟨5714242762566424224554573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15237980700177131265478861 5714242762566424224554573)
                  ·
                    refine ⟨2142841035962409084207965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5714242762566424224554573 2142841035962409084207965)
                    ·
                      refine ⟨803565388485903406577987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2142841035962409084207965 803565388485903406577987)
                      ·
                        rfl

theorem cell23_1564938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1564938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564938 prefixEnd_1564938 := by exact prefixLift 1564938
  have htrace : WordTrace (prefixWord ++ tailWord_1564938) baseStart_1564938 baseEnd_1564938 := by
    simpa [prefixWord, tailWord_1564938, baseEnd_1564938] using wordTrace_append hprefix tailTrace_1564938
  have hstable : (prefixWord ++ tailWord_1564938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564938).length < 2 ^ (prefixWord ++ tailWord_1564938).sum := by decide
  have hdescent : baseEnd_1564938 < baseStart_1564938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564955 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 3]
def baseStart_1564955 : Nat := 118140960795 + 1564955 * 2 ^ 59
def prefixEnd_1564955 : Nat := 4983230072969 + 3 ^ 40 * 1564955 * 2
def baseEnd_1564955 : Nat := 803574117657029840065409

theorem tailTrace_1564955 : CollatzResearch.WordTrace tailWord_1564955 prefixEnd_1564955 803574117657029840065409 := by
  unfold tailWord_1564955
  simp only [CollatzResearch.WordTrace]
  refine ⟨57078598045442782880416319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38052398696961855253610879 57078598045442782880416319)
  ·
    refine ⟨85617897068164174320624479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57078598045442782880416319 85617897068164174320624479)
    ·
      refine ⟨128426845602246261480936719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85617897068164174320624479 128426845602246261480936719)
      ·
        refine ⟨192640268403369392221405079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128426845602246261480936719 192640268403369392221405079)
        ·
          refine ⟨288960402605054088332107619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192640268403369392221405079 288960402605054088332107619)
          ·
            refine ⟨433440603907581132498161429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288960402605054088332107619 433440603907581132498161429)
            ·
              refine ⟨20317528308167865585851317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 433440603907581132498161429 20317528308167865585851317)
              ·
                refine ⟨1904768278890737398673561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20317528308167865585851317 1904768278890737398673561)
                ·
                  refine ⟨1428576209168053049005171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904768278890737398673561 1428576209168053049005171)
                  ·
                    refine ⟨2142864313752079573507757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428576209168053049005171 2142864313752079573507757)
                    ·
                      refine ⟨803574117657029840065409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2142864313752079573507757 803574117657029840065409)
                      ·
                        rfl

theorem cell23_1564955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 3].length) (baseStart_1564955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1564955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1564955 prefixEnd_1564955 := by exact prefixLift 1564955
  have htrace : WordTrace (prefixWord ++ tailWord_1564955) baseStart_1564955 baseEnd_1564955 := by
    simpa [prefixWord, tailWord_1564955, baseEnd_1564955] using wordTrace_append hprefix tailTrace_1564955
  have hstable : (prefixWord ++ tailWord_1564955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564955).length < 2 ^ (prefixWord ++ tailWord_1564955).sum := by decide
  have hdescent : baseEnd_1564955 < baseStart_1564955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565082 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_1565082 : Nat := 118140960795 + 1565082 * 2 ^ 59
def prefixEnd_1565082 : Nat := 4983230072969 + 3 ^ 40 * 1565082 * 2
def baseEnd_1565082 : Nat := 267879776566716947725775

theorem tailTrace_1565082 : CollatzResearch.WordTrace tailWord_1565082 prefixEnd_1565082 267879776566716947725775 := by
  unfold tailWord_1565082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14270807528995670892572375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38055486743988455713526333 14270807528995670892572375)
  ·
    refine ⟨21406211293493506338858563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14270807528995670892572375 21406211293493506338858563)
    ·
      refine ⟨32109316940240259508287845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21406211293493506338858563 32109316940240259508287845)
      ·
        refine ⟨6020496926295048657803971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32109316940240259508287845 6020496926295048657803971)
        ·
          refine ⟨9030745389442572986705957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020496926295048657803971 9030745389442572986705957)
          ·
            refine ⟨1693264760520482435007367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9030745389442572986705957 1693264760520482435007367)
            ·
              refine ⟨2539897140780723652511051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693264760520482435007367 2539897140780723652511051)
              ·
                refine ⟨3809845711171085478766577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539897140780723652511051 3809845711171085478766577)
                ·
                  refine ⟨2857384283378314109074933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3809845711171085478766577 2857384283378314109074933)
                  ·
                    refine ⟨267879776566716947725775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2857384283378314109074933 267879776566716947725775)
                    ·
                      rfl

theorem cell23_1565082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_1565082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565082 prefixEnd_1565082 := by exact prefixLift 1565082
  have htrace : WordTrace (prefixWord ++ tailWord_1565082) baseStart_1565082 baseEnd_1565082 := by
    simpa [prefixWord, tailWord_1565082, baseEnd_1565082] using wordTrace_append hprefix tailTrace_1565082
  have hstable : (prefixWord ++ tailWord_1565082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565082).length < 2 ^ (prefixWord ++ tailWord_1565082).sum := by decide
  have hdescent : baseEnd_1565082 < baseStart_1565082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565212 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1565212 : Nat := 118140960795 + 1565212 * 2 ^ 59
def prefixEnd_1565212 : Nat := 4983230072969 + 3 ^ 40 * 1565212 * 2
def baseEnd_1565212 : Nat := 803706082185235334551727

theorem tailTrace_1565212 : CollatzResearch.WordTrace tailWord_1565212 prefixEnd_1565212 803706082185235334551727 := by
  unfold tailWord_1565212
  simp only [CollatzResearch.WordTrace]
  refine ⟨28543985802755857886260945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38058647737007810515014593 28543985802755857886260945)
  ·
    refine ⟨21407989352066893414695709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28543985802755857886260945 21407989352066893414695709)
    ·
      refine ⟨8027996007025085030510891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21407989352066893414695709 8027996007025085030510891)
      ·
        refine ⟨12041994010537627545766337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8027996007025085030510891 12041994010537627545766337)
        ·
          refine ⟨9031495507903220659324753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12041994010537627545766337 9031495507903220659324753)
          ·
            refine ⟨6773621630927415494493565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031495507903220659324753 6773621630927415494493565)
            ·
              refine ⟨2540108111597780810435087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6773621630927415494493565 2540108111597780810435087)
              ·
                refine ⟨3810162167396671215652631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540108111597780810435087 3810162167396671215652631)
                ·
                  refine ⟨5715243251095006823478947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810162167396671215652631 5715243251095006823478947)
                  ·
                    refine ⟨8572864876642510235218421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715243251095006823478947 8572864876642510235218421)
                    ·
                      refine ⟨803706082185235334551727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8572864876642510235218421 803706082185235334551727)
                      ·
                        rfl

theorem cell23_1565212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1565212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565212 prefixEnd_1565212 := by exact prefixLift 1565212
  have htrace : WordTrace (prefixWord ++ tailWord_1565212) baseStart_1565212 baseEnd_1565212 := by
    simpa [prefixWord, tailWord_1565212, baseEnd_1565212] using wordTrace_append hprefix tailTrace_1565212
  have hstable : (prefixWord ++ tailWord_1565212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565212).length < 2 ^ (prefixWord ++ tailWord_1565212).sum := by decide
  have hdescent : baseEnd_1565212 < baseStart_1565212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565219 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 2, 4]
def baseStart_1565219 : Nat := 118140960795 + 1565219 * 2 ^ 59
def prefixEnd_1565219 : Nat := 4983230072969 + 3 ^ 40 * 1565219 * 2
def baseEnd_1565219 : Nat := 267903225516605602388065

theorem tailTrace_1565219 : CollatzResearch.WordTrace tailWord_1565219 prefixEnd_1565219 267903225516605602388065 := by
  unfold tailWord_1565219
  simp only [CollatzResearch.WordTrace]
  refine ⟨57088226916486355968026711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38058817944324237312017807 57088226916486355968026711)
  ·
    refine ⟨85632340374729533952040067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57088226916486355968026711 85632340374729533952040067)
    ·
      refine ⟨128448510562094300928060101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85632340374729533952040067 128448510562094300928060101)
      ·
        refine ⟨24084095730392681424011269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128448510562094300928060101 24084095730392681424011269)
        ·
          refine ⟨4515767949448627767002113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24084095730392681424011269 4515767949448627767002113)
          ·
            refine ⟨3386825962086470825251585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4515767949448627767002113 3386825962086470825251585)
            ·
              refine ⟨2540119471564853118938689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386825962086470825251585 2540119471564853118938689)
              ·
                refine ⟨1905089603673639839204017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540119471564853118938689 1905089603673639839204017)
                ·
                  refine ⟨1428817202755229879403013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905089603673639839204017 1428817202755229879403013)
                  ·
                    refine ⟨267903225516605602388065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428817202755229879403013 267903225516605602388065)
                    ·
                      rfl

theorem cell23_1565219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 4].length) (baseStart_1565219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565219 prefixEnd_1565219 := by exact prefixLift 1565219
  have htrace : WordTrace (prefixWord ++ tailWord_1565219) baseStart_1565219 baseEnd_1565219 := by
    simpa [prefixWord, tailWord_1565219, baseEnd_1565219] using wordTrace_append hprefix tailTrace_1565219
  have hstable : (prefixWord ++ tailWord_1565219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565219).length < 2 ^ (prefixWord ++ tailWord_1565219).sum := by decide
  have hdescent : baseEnd_1565219 < baseStart_1565219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565236 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1565236 : Nat := 118140960795 + 1565236 * 2 ^ 59
def prefixEnd_1565236 : Nat := 4983230072969 + 3 ^ 40 * 1565236 * 2
def baseEnd_1565236 : Nat := 267906135240314413550539

theorem tailTrace_1565236 : CollatzResearch.WordTrace tailWord_1565236 prefixEnd_1565236 267906135240314413550539 := by
  unfold tailWord_1565236
  simp only [CollatzResearch.WordTrace]
  refine ⟨28544423478712383935697781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38059231304949845247597041 28544423478712383935697781)
  ·
    refine ⟨2676039701129285993971667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28544423478712383935697781 2676039701129285993971667)
    ·
      refine ⟨4014059551693928990957501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676039701129285993971667 4014059551693928990957501)
      ·
        refine ⟨1505272331885223371609063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4014059551693928990957501 1505272331885223371609063)
        ·
          refine ⟨2257908497827835057413595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505272331885223371609063 2257908497827835057413595)
          ·
            refine ⟨3386862746741752586120393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257908497827835057413595 3386862746741752586120393)
            ·
              refine ⟨2540147060056314439590295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386862746741752586120393 2540147060056314439590295)
              ·
                refine ⟨3810220590084471659385443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540147060056314439590295 3810220590084471659385443)
                ·
                  refine ⟨5715330885126707489078165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810220590084471659385443 5715330885126707489078165)
                  ·
                    refine ⟨267906135240314413550539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5715330885126707489078165 267906135240314413550539)
                    ·
                      rfl

theorem cell23_1565236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1565236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565236 prefixEnd_1565236 := by exact prefixLift 1565236
  have htrace : WordTrace (prefixWord ++ tailWord_1565236) baseStart_1565236 baseEnd_1565236 := by
    simpa [prefixWord, tailWord_1565236, baseEnd_1565236] using wordTrace_append hprefix tailTrace_1565236
  have hstable : (prefixWord ++ tailWord_1565236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565236).length < 2 ^ (prefixWord ++ tailWord_1565236).sum := by decide
  have hdescent : baseEnd_1565236 < baseStart_1565236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565242 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_1565242 : Nat := 118140960795 + 1565242 * 2 ^ 59
def prefixEnd_1565242 : Nat := 4983230072969 + 3 ^ 40 * 1565242 * 2
def baseEnd_1565242 : Nat := 803721486604870217176589

theorem tailTrace_1565242 : CollatzResearch.WordTrace tailWord_1565242 prefixEnd_1565242 803721486604870217176589 := by
  unfold tailWord_1565242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14272266448850757724028495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38059377196935353930742653 14272266448850757724028495)
  ·
    refine ⟨21408399673276136586042743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14272266448850757724028495 21408399673276136586042743)
    ·
      refine ⟨32112599509914204879064115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21408399673276136586042743 32112599509914204879064115)
      ·
        refine ⟨48168899264871307318596173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32112599509914204879064115 48168899264871307318596173)
        ·
          refine ⟨18063337224326740244473565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48168899264871307318596173 18063337224326740244473565)
          ·
            refine ⟨6773751459122527591677587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18063337224326740244473565 6773751459122527591677587)
            ·
              refine ⟨10160627188683791387516381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773751459122527591677587 10160627188683791387516381)
              ·
                refine ⟨3810235195756421770318643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10160627188683791387516381 3810235195756421770318643)
                ·
                  refine ⟨5715352793634632655477965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810235195756421770318643 5715352793634632655477965)
                  ·
                    refine ⟨2143257297612987245804237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5715352793634632655477965 2143257297612987245804237)
                    ·
                      refine ⟨803721486604870217176589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2143257297612987245804237 803721486604870217176589)
                      ·
                        rfl

theorem cell23_1565242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_1565242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565242 prefixEnd_1565242 := by exact prefixLift 1565242
  have htrace : WordTrace (prefixWord ++ tailWord_1565242) baseStart_1565242 baseEnd_1565242 := by
    simpa [prefixWord, tailWord_1565242, baseEnd_1565242] using wordTrace_append hprefix tailTrace_1565242
  have hstable : (prefixWord ++ tailWord_1565242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565242).length < 2 ^ (prefixWord ++ tailWord_1565242).sum := by decide
  have hdescent : baseEnd_1565242 < baseStart_1565242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565276 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1565276 : Nat := 118140960795 + 1565276 * 2 ^ 59
def prefixEnd_1565276 : Nat := 4983230072969 + 3 ^ 40 * 1565276 * 2
def baseEnd_1565276 : Nat := 803738944947123084151433

theorem tailTrace_1565276 : CollatzResearch.WordTrace tailWord_1565276 prefixEnd_1565276 803738944947123084151433 := by
  unfold tailWord_1565276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545152938639927351425841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38060203918186569801901121 28545152938639927351425841)
  ·
    refine ⟨21408864703979945513569381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28545152938639927351425841 21408864703979945513569381)
    ·
      refine ⟨4014162131996239783794259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21408864703979945513569381 4014162131996239783794259)
      ·
        refine ⟨6021243197994359675691389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014162131996239783794259 6021243197994359675691389)
        ·
          refine ⟨2257966199247884878384271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6021243197994359675691389 2257966199247884878384271)
          ·
            refine ⟨3386949298871827317576407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257966199247884878384271 3386949298871827317576407)
            ·
              refine ⟨5080423948307740976364611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386949298871827317576407 5080423948307740976364611)
              ·
                refine ⟨7620635922461611464546917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080423948307740976364611 7620635922461611464546917)
                ·
                  refine ⟨1428869235461552149602547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7620635922461611464546917 1428869235461552149602547)
                  ·
                    refine ⟨2143303853192328224403821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428869235461552149602547 2143303853192328224403821)
                    ·
                      refine ⟨803738944947123084151433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2143303853192328224403821 803738944947123084151433)
                      ·
                        rfl

theorem cell23_1565276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1565276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565276 prefixEnd_1565276 := by exact prefixLift 1565276
  have htrace : WordTrace (prefixWord ++ tailWord_1565276) baseStart_1565276 baseEnd_1565276 := by
    simpa [prefixWord, tailWord_1565276, baseEnd_1565276] using wordTrace_append hprefix tailTrace_1565276
  have hstable : (prefixWord ++ tailWord_1565276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565276).length < 2 ^ (prefixWord ++ tailWord_1565276).sum := by decide
  have hdescent : baseEnd_1565276 < baseStart_1565276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565293 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_1565293 : Nat := 118140960795 + 1565293 * 2 ^ 59
def prefixEnd_1565293 : Nat := 4983230072969 + 3 ^ 40 * 1565293 * 2
def baseEnd_1565293 : Nat := 803747674118249517638855

theorem tailTrace_1565293 : CollatzResearch.WordTrace tailWord_1565293 prefixEnd_1565293 803747674118249517638855 := by
  unfold tailWord_1565293
  simp only [CollatzResearch.WordTrace]
  refine ⟨57090925918218266606220533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38060617278812177737480355 57090925918218266606220533)
  ·
    refine ⟨5352274304832962494333175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57090925918218266606220533 5352274304832962494333175)
    ·
      refine ⟨8028411457249443741499763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5352274304832962494333175 8028411457249443741499763)
      ·
        refine ⟨12042617185874165612249645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8028411457249443741499763 12042617185874165612249645)
        ·
          refine ⟨4515981444702812104593617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12042617185874165612249645 4515981444702812104593617)
          ·
            refine ⟨3386986083527109078445213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4515981444702812104593617 3386986083527109078445213)
            ·
              refine ⟨1270119781322665904416955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3386986083527109078445213 1270119781322665904416955)
              ·
                refine ⟨1905179671983998856625433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270119781322665904416955 1905179671983998856625433)
                ·
                  refine ⟨1428884753987999142469075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905179671983998856625433 1428884753987999142469075)
                  ·
                    refine ⟨2143327130981998713703613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428884753987999142469075 2143327130981998713703613)
                    ·
                      refine ⟨803747674118249517638855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2143327130981998713703613 803747674118249517638855)
                      ·
                        rfl

theorem cell23_1565293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_1565293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565293 prefixEnd_1565293 := by exact prefixLift 1565293
  have htrace : WordTrace (prefixWord ++ tailWord_1565293) baseStart_1565293 baseEnd_1565293 := by
    simpa [prefixWord, tailWord_1565293, baseEnd_1565293] using wordTrace_append hprefix tailTrace_1565293
  have hstable : (prefixWord ++ tailWord_1565293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565293).length < 2 ^ (prefixWord ++ tailWord_1565293).sum := by decide
  have hdescent : baseEnd_1565293 < baseStart_1565293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565316 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_1565316 : Nat := 118140960795 + 1565316 * 2 ^ 59
def prefixEnd_1565316 : Nat := 4983230072969 + 3 ^ 40 * 1565316 * 2
def baseEnd_1565316 : Nat := 803759484173302927651249

theorem tailTrace_1565316 : CollatzResearch.WordTrace tailWord_1565316 prefixEnd_1565316 803759484173302927651249 := by
  unfold tailWord_1565316
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545882398567470767153901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38061176531423294356205201 28545882398567470767153901)
  ·
    refine ⟨10704705899462801537682713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28545882398567470767153901 10704705899462801537682713)
    ·
      refine ⟨8028529424597101153262035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10704705899462801537682713 8028529424597101153262035)
      ·
        refine ⟨12042794136895651729893053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8028529424597101153262035 12042794136895651729893053)
        ·
          refine ⟨4516047801335869398709895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12042794136895651729893053 4516047801335869398709895)
          ·
            refine ⟨6774071702003804098064843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516047801335869398709895 6774071702003804098064843)
            ·
              refine ⟨10161107553005706147097265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774071702003804098064843 10161107553005706147097265)
              ·
                refine ⟨7620830664754279610322949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10161107553005706147097265 7620830664754279610322949)
                ·
                  refine ⟨1428905749641427426935553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7620830664754279610322949 1428905749641427426935553)
                  ·
                    refine ⟨1071679312231070570201665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428905749641427426935553 1071679312231070570201665)
                    ·
                      refine ⟨803759484173302927651249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071679312231070570201665 803759484173302927651249)
                      ·
                        rfl

theorem cell23_1565316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_1565316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565316 prefixEnd_1565316 := by exact prefixLift 1565316
  have htrace : WordTrace (prefixWord ++ tailWord_1565316) baseStart_1565316 baseEnd_1565316 := by
    simpa [prefixWord, tailWord_1565316, baseEnd_1565316] using wordTrace_append hprefix tailTrace_1565316
  have hstable : (prefixWord ++ tailWord_1565316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565316).length < 2 ^ (prefixWord ++ tailWord_1565316).sum := by decide
  have hdescent : baseEnd_1565316 < baseStart_1565316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565416 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1565416 : Nat := 118140960795 + 1565416 * 2 ^ 59
def prefixEnd_1565416 : Nat := 4983230072969 + 3 ^ 40 * 1565416 * 2
def baseEnd_1565416 : Nat := 267936944079584178800263

theorem tailTrace_1565416 : CollatzResearch.WordTrace tailWord_1565416 prefixEnd_1565416 267936944079584178800263 := by
  unfold tailWord_1565416
  simp only [CollatzResearch.WordTrace]
  refine ⟨28547706048386329306474051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38063608064515105741965401 28547706048386329306474051)
  ·
    refine ⟨42821559072579493959711077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28547706048386329306474051 42821559072579493959711077)
    ·
      refine ⟨8029042326108655117445827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42821559072579493959711077 8029042326108655117445827)
      ·
        refine ⟨12043563489162982676168741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8029042326108655117445827 12043563489162982676168741)
        ·
          refine ⟨2258168154218059251781639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12043563489162982676168741 2258168154218059251781639)
          ·
            refine ⟨3387252231327088877672459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258168154218059251781639 3387252231327088877672459)
            ·
              refine ⟨5080878346990633316508689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387252231327088877672459 5080878346990633316508689)
              ·
                refine ⟨3810658760242974987381517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5080878346990633316508689 3810658760242974987381517)
                ·
                  refine ⟨1428997035091115620268069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3810658760242974987381517 1428997035091115620268069)
                  ·
                    refine ⟨267936944079584178800263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428997035091115620268069 267936944079584178800263)
                    ·
                      rfl

theorem cell23_1565416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1565416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565416 prefixEnd_1565416 := by exact prefixLift 1565416
  have htrace : WordTrace (prefixWord ++ tailWord_1565416) baseStart_1565416 baseEnd_1565416 := by
    simpa [prefixWord, tailWord_1565416, baseEnd_1565416] using wordTrace_append hprefix tailTrace_1565416
  have hstable : (prefixWord ++ tailWord_1565416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565416).length < 2 ^ (prefixWord ++ tailWord_1565416).sum := by decide
  have hdescent : baseEnd_1565416 < baseStart_1565416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565426 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1565426 : Nat := 118140960795 + 1565426 * 2 ^ 59
def prefixEnd_1565426 : Nat := 4983230072969 + 3 ^ 40 * 1565426 * 2
def baseEnd_1565426 : Nat := 803815967045297497275743

theorem tailTrace_1565426 : CollatzResearch.WordTrace tailWord_1565426 prefixEnd_1565426 803815967045297497275743 := by
  unfold tailWord_1565426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273944206684107580203033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38063851217824286880541421 14273944206684107580203033)
  ·
    refine ⟨10705458155013080685152275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14273944206684107580203033 10705458155013080685152275)
    ·
      refine ⟨16058187232519621027728413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10705458155013080685152275 16058187232519621027728413)
      ·
        refine ⟨6021820212194857885398155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16058187232519621027728413 6021820212194857885398155)
        ·
          refine ⟨9032730318292286828097233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021820212194857885398155 9032730318292286828097233)
          ·
            refine ⟨6774547738719215121072925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9032730318292286828097233 6774547738719215121072925)
            ·
              refine ⟨2540455402019705670402347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6774547738719215121072925 2540455402019705670402347)
              ·
                refine ⟨3810683103029558505603521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540455402019705670402347 3810683103029558505603521)
                ·
                  refine ⟨2858012327272168879202641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3810683103029558505603521 2858012327272168879202641)
                  ·
                    refine ⟨2143509245454126659401981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2858012327272168879202641 2143509245454126659401981)
                    ·
                      refine ⟨803815967045297497275743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2143509245454126659401981 803815967045297497275743)
                      ·
                        rfl

theorem cell23_1565426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1565426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565426 prefixEnd_1565426 := by exact prefixLift 1565426
  have htrace : WordTrace (prefixWord ++ tailWord_1565426) baseStart_1565426 baseEnd_1565426 := by
    simpa [prefixWord, tailWord_1565426, baseEnd_1565426] using wordTrace_append hprefix tailTrace_1565426
  have hstable : (prefixWord ++ tailWord_1565426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565426).length < 2 ^ (prefixWord ++ tailWord_1565426).sum := by decide
  have hdescent : baseEnd_1565426 < baseStart_1565426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565439 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 3]
def baseStart_1565439 : Nat := 118140960795 + 1565439 * 2 ^ 59
def prefixEnd_1565439 : Nat := 4983230072969 + 3 ^ 40 * 1565439 * 2
def baseEnd_1565439 : Nat := 803822642293805946413183

theorem tailTrace_1565439 : CollatzResearch.WordTrace tailWord_1565439 prefixEnd_1565439 803822642293805946413183 := by
  unfold tailWord_1565439
  simp only [CollatzResearch.WordTrace]
  refine ⟨57096250975689333541035371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38064167317126222360690247 57096250975689333541035371)
  ·
    refine ⟨85644376463534000311553057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57096250975689333541035371 85644376463534000311553057)
    ·
      refine ⟨64233282347650500233664793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85644376463534000311553057 64233282347650500233664793)
      ·
        refine ⟨48174961760737875175248595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64233282347650500233664793 48174961760737875175248595)
        ·
          refine ⟨72262442641106812762872893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48174961760737875175248595 72262442641106812762872893)
          ·
            refine ⟨27098415990415054786077335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72262442641106812762872893 27098415990415054786077335)
            ·
              refine ⟨40647623985622582179116003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27098415990415054786077335 40647623985622582179116003)
              ·
                refine ⟨60971435978433873268674005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40647623985622582179116003 60971435978433873268674005)
                ·
                  refine ⟨1429018030744543904734547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60971435978433873268674005 1429018030744543904734547)
                  ·
                    refine ⟨2143527046116815857101821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1429018030744543904734547 2143527046116815857101821)
                    ·
                      refine ⟨803822642293805946413183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2143527046116815857101821 803822642293805946413183)
                      ·
                        rfl

theorem cell23_1565439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_1565439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565439 prefixEnd_1565439 := by exact prefixLift 1565439
  have htrace : WordTrace (prefixWord ++ tailWord_1565439) baseStart_1565439 baseEnd_1565439 := by
    simpa [prefixWord, tailWord_1565439, baseEnd_1565439] using wordTrace_append hprefix tailTrace_1565439
  have hstable : (prefixWord ++ tailWord_1565439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565439).length < 2 ^ (prefixWord ++ tailWord_1565439).sum := by decide
  have hdescent : baseEnd_1565439 < baseStart_1565439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565489 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 6, 4]
def baseStart_1565489 : Nat := 118140960795 + 1565489 * 2 ^ 59
def prefixEnd_1565489 : Nat := 4983230072969 + 3 ^ 40 * 1565489 * 2
def baseEnd_1565489 : Nat := 267949438775510250262651

theorem tailTrace_1565489 : CollatzResearch.WordTrace tailWord_1565489 prefixEnd_1565489 267949438775510250262651 := by
  unfold tailWord_1565489
  simp only [CollatzResearch.WordTrace]
  refine ⟨57098074625508192080355521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38065383083672128053570347 57098074625508192080355521)
  ·
    refine ⟨42823555969131144060266641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57098074625508192080355521 42823555969131144060266641)
    ·
      refine ⟨32117666976848358045199981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42823555969131144060266641 32117666976848358045199981)
      ·
        refine ⟨12044125116318134266949993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32117666976848358045199981 12044125116318134266949993)
        ·
          refine ⟨9033093837238600700212495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12044125116318134266949993 9033093837238600700212495)
          ·
            refine ⟨13549640755857901050318743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033093837238600700212495 13549640755857901050318743)
            ·
              refine ⟨20324461133786851575478115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13549640755857901050318743 20324461133786851575478115)
              ·
                refine ⟨30486691700680277363217173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20324461133786851575478115 30486691700680277363217173)
                ·
                  refine ⟨1429063673469388001400805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30486691700680277363217173 1429063673469388001400805)
                  ·
                    refine ⟨267949438775510250262651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429063673469388001400805 267949438775510250262651)
                    ·
                      rfl

theorem cell23_1565489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_1565489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565489 prefixEnd_1565489 := by exact prefixLift 1565489
  have htrace : WordTrace (prefixWord ++ tailWord_1565489) baseStart_1565489 baseEnd_1565489 := by
    simpa [prefixWord, tailWord_1565489, baseEnd_1565489] using wordTrace_append hprefix tailTrace_1565489
  have hstable : (prefixWord ++ tailWord_1565489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565489).length < 2 ^ (prefixWord ++ tailWord_1565489).sum := by decide
  have hdescent : baseEnd_1565489 < baseStart_1565489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565513 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 3, 2, 2]
def baseStart_1565513 : Nat := 118140960795 + 1565513 * 2 ^ 59
def prefixEnd_1565513 : Nat := 4983230072969 + 3 ^ 40 * 1565513 * 2
def baseEnd_1565513 : Nat := 803860639862238656887843

theorem tailTrace_1565513 : CollatzResearch.WordTrace tailWord_1565513 prefixEnd_1565513 803860639862238656887843 := by
  unfold tailWord_1565513
  simp only [CollatzResearch.WordTrace]
  refine ⟨57098949977421244179229193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38065966651614162786152795 57098949977421244179229193)
  ·
    refine ⟨42824212483065933134421895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57098949977421244179229193 42824212483065933134421895)
    ·
      refine ⟨64236318724598899701632843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42824212483065933134421895 64236318724598899701632843)
      ·
        refine ⟨96354478086898349552449265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64236318724598899701632843 96354478086898349552449265)
        ·
          refine ⟨72265858565173762164336949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96354478086898349552449265 72265858565173762164336949)
          ·
            refine ⟨6774924240485040202906589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72265858565173762164336949 6774924240485040202906589)
            ·
              refine ⟨2540596590181890076089971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6774924240485040202906589 2540596590181890076089971)
              ·
                refine ⟨3810894885272835114134957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540596590181890076089971 3810894885272835114134957)
                ·
                  refine ⟨1429085581977313167800609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3810894885272835114134957 1429085581977313167800609)
                  ·
                    refine ⟨1071814186482984875850457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1429085581977313167800609 1071814186482984875850457)
                    ·
                      refine ⟨803860639862238656887843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071814186482984875850457 803860639862238656887843)
                      ·
                        rfl

theorem cell23_1565513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 2, 2].length) (baseStart_1565513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565513 prefixEnd_1565513 := by exact prefixLift 1565513
  have htrace : WordTrace (prefixWord ++ tailWord_1565513) baseStart_1565513 baseEnd_1565513 := by
    simpa [prefixWord, tailWord_1565513, baseEnd_1565513] using wordTrace_append hprefix tailTrace_1565513
  have hstable : (prefixWord ++ tailWord_1565513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565513).length < 2 ^ (prefixWord ++ tailWord_1565513).sum := by decide
  have hdescent : baseEnd_1565513 < baseStart_1565513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565550 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1565550 : Nat := 118140960795 + 1565550 * 2 ^ 59
def prefixEnd_1565550 : Nat := 4983230072969 + 3 ^ 40 * 1565550 * 2
def baseEnd_1565550 : Nat := 803879638646455012125173

theorem tailTrace_1565550 : CollatzResearch.WordTrace tailWord_1565550 prefixEnd_1565550 803879638646455012125173 := by
  unfold tailWord_1565550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137537434785899937290763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38066866318858132998884069 7137537434785899937290763)
  ·
    refine ⟨10706306152178849905936145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7137537434785899937290763 10706306152178849905936145)
    ·
      refine ⟨8029729614134137429452109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10706306152178849905936145 8029729614134137429452109)
      ·
        refine ⟨3011148605300301536044541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8029729614134137429452109 3011148605300301536044541)
        ·
          refine ⟨1129180726987613076016703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3011148605300301536044541 1129180726987613076016703)
          ·
            refine ⟨1693771090481419614025055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129180726987613076016703 1693771090481419614025055)
            ·
              refine ⟨2540656635722129421037583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693771090481419614025055 2540656635722129421037583)
              ·
                refine ⟨3810984953583194131556375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540656635722129421037583 3810984953583194131556375)
                ·
                  refine ⟨5716477430374791197334563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810984953583194131556375 5716477430374791197334563)
                  ·
                    refine ⟨8574716145562186796001845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716477430374791197334563 8574716145562186796001845)
                    ·
                      refine ⟨803879638646455012125173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8574716145562186796001845 803879638646455012125173)
                      ·
                        rfl

theorem cell23_1565550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1565550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565550 prefixEnd_1565550 := by exact prefixLift 1565550
  have htrace : WordTrace (prefixWord ++ tailWord_1565550) baseStart_1565550 baseEnd_1565550 := by
    simpa [prefixWord, tailWord_1565550, baseEnd_1565550] using wordTrace_append hprefix tailTrace_1565550
  have hstable : (prefixWord ++ tailWord_1565550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565550).length < 2 ^ (prefixWord ++ tailWord_1565550).sum := by decide
  have hdescent : baseEnd_1565550 < baseStart_1565550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565570 : List Nat := [3, 4, 2, 2, 1, 2, 1, 8]
def baseStart_1565570 : Nat := 118140960795 + 1565570 * 2 ^ 59
def prefixEnd_1565570 : Nat := 4983230072969 + 3 ^ 40 * 1565570 * 2
def baseEnd_1565570 : Nat := 29773700305909071625003

theorem tailTrace_1565570 : CollatzResearch.WordTrace tailWord_1565570 prefixEnd_1565570 29773700305909071625003 := by
  unfold tailWord_1565570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275257234553685728513541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38067352625476495276036109 14275257234553685728513541)
  ·
    refine ⟨2676610731478816074096289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14275257234553685728513541 2676610731478816074096289)
    ·
      refine ⟨2007458048609112055572217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2676610731478816074096289 2007458048609112055572217)
      ·
        refine ⟨1505593536456834041679163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2007458048609112055572217 1505593536456834041679163)
        ·
          refine ⟨2258390304685251062518745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505593536456834041679163 2258390304685251062518745)
          ·
            refine ⟨1693792728513938296889059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2258390304685251062518745 1693792728513938296889059)
            ·
              refine ⟨2540689092770907445333589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693792728513938296889059 2540689092770907445333589)
              ·
                refine ⟨29773700305909071625003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2540689092770907445333589 29773700305909071625003)
                ·
                  rfl

theorem cell23_1565570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_1565570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565570 prefixEnd_1565570 := by exact prefixLift 1565570
  have htrace : WordTrace (prefixWord ++ tailWord_1565570) baseStart_1565570 baseEnd_1565570 := by
    simpa [prefixWord, tailWord_1565570, baseEnd_1565570] using wordTrace_append hprefix tailTrace_1565570
  have hstable : (prefixWord ++ tailWord_1565570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565570).length < 2 ^ (prefixWord ++ tailWord_1565570).sum := by decide
  have hdescent : baseEnd_1565570 < baseStart_1565570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565626 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_1565626 : Nat := 118140960795 + 1565626 * 2 ^ 59
def prefixEnd_1565626 : Nat := 4983230072969 + 3 ^ 40 * 1565626 * 2
def baseEnd_1565626 : Nat := 89324295908466301641647

theorem tailTrace_1565626 : CollatzResearch.WordTrace tailWord_1565626 prefixEnd_1565626 89324295908466301641647 := by
  unfold tailWord_1565626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275767856502966119523183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38068714284007909652061821 14275767856502966119523183)
  ·
    refine ⟨21413651784754449179284775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14275767856502966119523183 21413651784754449179284775)
    ·
      refine ⟨32120477677131673768927163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21413651784754449179284775 32120477677131673768927163)
      ·
        refine ⟨48180716515697510653390745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32120477677131673768927163 48180716515697510653390745)
        ·
          refine ⟨36135537386773132990043059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48180716515697510653390745 36135537386773132990043059)
          ·
            refine ⟨54203306080159699485064589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36135537386773132990043059 54203306080159699485064589)
            ·
              refine ⟨20326239780059887306899221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54203306080159699485064589 20326239780059887306899221)
              ·
                refine ⟨952792489690307217510901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20326239780059887306899221 952792489690307217510901)
                ·
                  refine ⟨89324295908466301641647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952792489690307217510901 89324295908466301641647)
                  ·
                    rfl

theorem cell23_1565626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_1565626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565626 prefixEnd_1565626 := by exact prefixLift 1565626
  have htrace : WordTrace (prefixWord ++ tailWord_1565626) baseStart_1565626 baseEnd_1565626 := by
    simpa [prefixWord, tailWord_1565626, baseEnd_1565626] using wordTrace_append hprefix tailTrace_1565626
  have hstable : (prefixWord ++ tailWord_1565626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565626).length < 2 ^ (prefixWord ++ tailWord_1565626).sum := by decide
  have hdescent : baseEnd_1565626 < baseStart_1565626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565639 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1565639 : Nat := 118140960795 + 1565639 * 2 ^ 59
def prefixEnd_1565639 : Nat := 4983230072969 + 3 ^ 40 * 1565639 * 2
def baseEnd_1565639 : Nat := 267975112808235054637421

theorem tailTrace_1565639 : CollatzResearch.WordTrace tailWord_1565639 prefixEnd_1565639 267975112808235054637421 := by
  unfold tailWord_1565639
  simp only [CollatzResearch.WordTrace]
  refine ⟨57103545574964767698315971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38069030383309845132210647 57103545574964767698315971)
  ·
    refine ⟨85655318362447151547473957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57103545574964767698315971 85655318362447151547473957)
    ·
      refine ⟨16060372192958840915151367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85655318362447151547473957 16060372192958840915151367)
      ·
        refine ⟨24090558289438261372727051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16060372192958840915151367 24090558289438261372727051)
        ·
          refine ⟨36135837434157392059090577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24090558289438261372727051 36135837434157392059090577)
          ·
            refine ⟨27101878075618044044317933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36135837434157392059090577 27101878075618044044317933)
            ·
              refine ⟨10163204278356766516619225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27101878075618044044317933 10163204278356766516619225)
              ·
                refine ⟨7622403208767574887464419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10163204278356766516619225 7622403208767574887464419)
                ·
                  refine ⟨11433604813151362331196629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622403208767574887464419 11433604813151362331196629)
                  ·
                    refine ⟨267975112808235054637421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11433604813151362331196629 267975112808235054637421)
                    ·
                      rfl

theorem cell23_1565639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1565639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565639 prefixEnd_1565639 := by exact prefixLift 1565639
  have htrace : WordTrace (prefixWord ++ tailWord_1565639) baseStart_1565639 baseEnd_1565639 := by
    simpa [prefixWord, tailWord_1565639, baseEnd_1565639] using wordTrace_append hprefix tailTrace_1565639
  have hstable : (prefixWord ++ tailWord_1565639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565639).length < 2 ^ (prefixWord ++ tailWord_1565639).sum := by decide
  have hdescent : baseEnd_1565639 < baseStart_1565639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565746 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1565746 : Nat := 118140960795 + 1565746 * 2 ^ 59
def prefixEnd_1565746 : Nat := 4983230072969 + 3 ^ 40 * 1565746 * 2
def baseEnd_1565746 : Nat := 267993426951578748424757

theorem tailTrace_1565746 : CollatzResearch.WordTrace tailWord_1565746 prefixEnd_1565746 267993426951578748424757 := by
  unfold tailWord_1565746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14276862046394281243115273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38071632123718083314974061 14276862046394281243115273)
  ·
    refine ⟨10707646534795710932336455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14276862046394281243115273 10707646534795710932336455)
    ·
      refine ⟨16061469802193566398504683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10707646534795710932336455 16061469802193566398504683)
      ·
        refine ⟨24092204703290349597757025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061469802193566398504683 24092204703290349597757025)
        ·
          refine ⟨18069153527467762198317769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24092204703290349597757025 18069153527467762198317769)
          ·
            refine ⟨13551865145600821648738327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18069153527467762198317769 13551865145600821648738327)
            ·
              refine ⟨20327797718401232473107491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13551865145600821648738327 20327797718401232473107491)
              ·
                refine ⟨30491696577601848709661237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20327797718401232473107491 30491696577601848709661237)
                ·
                  refine ⟨2858596554150173316530741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30491696577601848709661237 2858596554150173316530741)
                  ·
                    refine ⟨267993426951578748424757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2858596554150173316530741 267993426951578748424757)
                    ·
                      rfl

theorem cell23_1565746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1565746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565746 prefixEnd_1565746 := by exact prefixLift 1565746
  have htrace : WordTrace (prefixWord ++ tailWord_1565746) baseStart_1565746 baseEnd_1565746 := by
    simpa [prefixWord, tailWord_1565746, baseEnd_1565746] using wordTrace_append hprefix tailTrace_1565746
  have hstable : (prefixWord ++ tailWord_1565746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565746).length < 2 ^ (prefixWord ++ tailWord_1565746).sum := by decide
  have hdescent : baseEnd_1565746 < baseStart_1565746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565770 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_1565770 : Nat := 118140960795 + 1565770 * 2 ^ 59
def prefixEnd_1565770 : Nat := 4983230072969 + 3 ^ 40 * 1565770 * 2
def baseEnd_1565770 : Nat := 803992604390444151374161

theorem tailTrace_1565770 : CollatzResearch.WordTrace tailWord_1565770 prefixEnd_1565770 803992604390444151374161 := by
  unfold tailWord_1565770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277080884372544267833691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38072215691660118047556509 14277080884372544267833691)
  ·
    refine ⟨21415621326558816401750537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14277080884372544267833691 21415621326558816401750537)
    ·
      refine ⟨16061715994919112301312903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21415621326558816401750537 16061715994919112301312903)
      ·
        refine ⟨24092573992378668451969355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061715994919112301312903 24092573992378668451969355)
        ·
          refine ⟨36138860988568002677954033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24092573992378668451969355 36138860988568002677954033)
          ·
            refine ⟨27104145741426002008465525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36138860988568002677954033 27104145741426002008465525)
            ·
              refine ⟨2541013663258687688293643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27104145741426002008465525 2541013663258687688293643)
              ·
                refine ⟨3811520494888031532440465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541013663258687688293643 3811520494888031532440465)
                ·
                  refine ⟨2858640371166023649330349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3811520494888031532440465 2858640371166023649330349)
                  ·
                    refine ⟨1071990139187258868498881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858640371166023649330349 1071990139187258868498881)
                    ·
                      refine ⟨803992604390444151374161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1071990139187258868498881 803992604390444151374161)
                      ·
                        rfl

theorem cell23_1565770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_1565770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565770 prefixEnd_1565770 := by exact prefixLift 1565770
  have htrace : WordTrace (prefixWord ++ tailWord_1565770) baseStart_1565770 baseEnd_1565770 := by
    simpa [prefixWord, tailWord_1565770, baseEnd_1565770] using wordTrace_append hprefix tailTrace_1565770
  have hstable : (prefixWord ++ tailWord_1565770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565770).length < 2 ^ (prefixWord ++ tailWord_1565770).sum := by decide
  have hdescent : baseEnd_1565770 < baseStart_1565770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565780 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1565780 : Nat := 118140960795 + 1565780 * 2 ^ 59
def prefixEnd_1565780 : Nat := 4983230072969 + 3 ^ 40 * 1565780 * 2
def baseEnd_1565780 : Nat := 267999246398996370749705

theorem tailTrace_1565780 : CollatzResearch.WordTrace tailWord_1565780 prefixEnd_1565780 267999246398996370749705 := by
  unfold tailWord_1565780
  simp only [CollatzResearch.WordTrace]
  refine ⟨28554344133726974389599397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38072458844969299186132529 28554344133726974389599397)
  ·
    refine ⟨5353939525073807698049887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28554344133726974389599397 5353939525073807698049887)
    ·
      refine ⟨8030909287610711547074831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5353939525073807698049887 8030909287610711547074831)
      ·
        refine ⟨12046363931416067320612247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030909287610711547074831 12046363931416067320612247)
        ·
          refine ⟨18069545897124100980918371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12046363931416067320612247 18069545897124100980918371)
          ·
            refine ⟨27104318845686151471377557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18069545897124100980918371 27104318845686151471377557)
            ·
              refine ⟨1270514945891538350220823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27104318845686151471377557 1270514945891538350220823)
              ·
                refine ⟨1905772418837307525331235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270514945891538350220823 1905772418837307525331235)
                ·
                  refine ⟨2858658628255961287996853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905772418837307525331235 2858658628255961287996853)
                  ·
                    refine ⟨267999246398996370749705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2858658628255961287996853 267999246398996370749705)
                    ·
                      rfl

theorem cell23_1565780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1565780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565780 prefixEnd_1565780 := by exact prefixLift 1565780
  have htrace : WordTrace (prefixWord ++ tailWord_1565780) baseStart_1565780 baseEnd_1565780 := by
    simpa [prefixWord, tailWord_1565780, baseEnd_1565780] using wordTrace_append hprefix tailTrace_1565780
  have hstable : (prefixWord ++ tailWord_1565780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565780).length < 2 ^ (prefixWord ++ tailWord_1565780).sum := by decide
  have hdescent : baseEnd_1565780 < baseStart_1565780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565794 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1565794 : Nat := 118140960795 + 1565794 * 2 ^ 59
def prefixEnd_1565794 : Nat := 4983230072969 + 3 ^ 40 * 1565794 * 2
def baseEnd_1565794 : Nat := 804004927926152057474051

theorem tailTrace_1565794 : CollatzResearch.WordTrace tailWord_1565794 prefixEnd_1565794 804004927926152057474051 := by
  unfold tailWord_1565794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277299722350807292552109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38072799259602152780138957 14277299722350807292552109)
  ·
    refine ⟨5353987395881552734707041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14277299722350807292552109 5353987395881552734707041)
    ·
      refine ⟨4015490546911164551030281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5353987395881552734707041 4015490546911164551030281)
      ·
        refine ⟨3011617910183373413272711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015490546911164551030281 3011617910183373413272711)
        ·
          refine ⟨4517426865275060119909067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011617910183373413272711 4517426865275060119909067)
          ·
            refine ⟨6776140297912590179863601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517426865275060119909067 6776140297912590179863601)
            ·
              refine ⟨5082105223434442634897701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6776140297912590179863601 5082105223434442634897701)
              ·
                refine ⟨952894729393957994043319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5082105223434442634897701 952894729393957994043319)
                ·
                  refine ⟨1429342094090936991064979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952894729393957994043319 1429342094090936991064979)
                  ·
                    refine ⟨2144013141136405486597469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1429342094090936991064979 2144013141136405486597469)
                    ·
                      refine ⟨804004927926152057474051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144013141136405486597469 804004927926152057474051)
                      ·
                        rfl

theorem cell23_1565794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1565794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565794 prefixEnd_1565794 := by exact prefixLift 1565794
  have htrace : WordTrace (prefixWord ++ tailWord_1565794) baseStart_1565794 baseEnd_1565794 := by
    simpa [prefixWord, tailWord_1565794, baseEnd_1565794] using wordTrace_append hprefix tailTrace_1565794
  have hstable : (prefixWord ++ tailWord_1565794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565794).length < 2 ^ (prefixWord ++ tailWord_1565794).sum := by decide
  have hdescent : baseEnd_1565794 < baseStart_1565794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565796 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_1565796 : Nat := 118140960795 + 1565796 * 2 ^ 59
def prefixEnd_1565796 : Nat := 4983230072969 + 3 ^ 40 * 1565796 * 2
def baseEnd_1565796 : Nat := 804005954887461049649041

theorem tailTrace_1565796 : CollatzResearch.WordTrace tailWord_1565796 prefixEnd_1565796 804005954887461049649041 := by
  unfold tailWord_1565796
  simp only [CollatzResearch.WordTrace]
  refine ⟨28554635917697991755890621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38072847890263989007854161 28554635917697991755890621)
  ·
    refine ⟨10707988469136746908458983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28554635917697991755890621 10707988469136746908458983)
    ·
      refine ⟨16061982703705120362688475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10707988469136746908458983 16061982703705120362688475)
      ·
        refine ⟨24092974055557680544032713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061982703705120362688475 24092974055557680544032713)
        ·
          refine ⟨18069730541668260408024535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24092974055557680544032713 18069730541668260408024535)
          ·
            refine ⟨27104595812502390612036803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18069730541668260408024535 27104595812502390612036803)
            ·
              refine ⟨40656893718753585918055205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27104595812502390612036803 40656893718753585918055205)
              ·
                refine ⟨7623167572266297359635351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40656893718753585918055205 7623167572266297359635351)
                ·
                  refine ⟨11434751358399446039453027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7623167572266297359635351 11434751358399446039453027)
                  ·
                    refine ⟨17152127037599169059179541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11434751358399446039453027 17152127037599169059179541)
                    ·
                      refine ⟨804005954887461049649041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17152127037599169059179541 804005954887461049649041)
                      ·
                        rfl

theorem cell23_1565796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_1565796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565796 prefixEnd_1565796 := by exact prefixLift 1565796
  have htrace : WordTrace (prefixWord ++ tailWord_1565796) baseStart_1565796 baseEnd_1565796 := by
    simpa [prefixWord, tailWord_1565796, baseEnd_1565796] using wordTrace_append hprefix tailTrace_1565796
  have hstable : (prefixWord ++ tailWord_1565796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565796).length < 2 ^ (prefixWord ++ tailWord_1565796).sum := by decide
  have hdescent : baseEnd_1565796 < baseStart_1565796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565820 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_1565820 : Nat := 118140960795 + 1565820 * 2 ^ 59
def prefixEnd_1565820 : Nat := 4983230072969 + 3 ^ 40 * 1565820 * 2
def baseEnd_1565820 : Nat := 804018278423168955748931

theorem tailTrace_1565820 : CollatzResearch.WordTrace tailWord_1565820 prefixEnd_1565820 804018278423168955748931 := by
  unfold tailWord_1565820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28555073593654517805327457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38073431458206023740436609 28555073593654517805327457)
  ·
    refine ⟨21416305195240888353995593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28555073593654517805327457 21416305195240888353995593)
    ·
      refine ⟨16062228896430666265496695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21416305195240888353995593 16062228896430666265496695)
      ·
        refine ⟨24093343344645999398245043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16062228896430666265496695 24093343344645999398245043)
        ·
          refine ⟨36140015016968999097367565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24093343344645999398245043 36140015016968999097367565)
          ·
            refine ⟨13552505631363374661512837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36140015016968999097367565 13552505631363374661512837)
            ·
              refine ⟨2541094805880632749033657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13552505631363374661512837 2541094805880632749033657)
              ·
                refine ⟨1905821104410474561775243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2541094805880632749033657 1905821104410474561775243)
                ·
                  refine ⟨2858731656615711842662865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905821104410474561775243 2858731656615711842662865)
                  ·
                    refine ⟨2144048742461783881997149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2858731656615711842662865 2144048742461783881997149)
                    ·
                      refine ⟨804018278423168955748931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144048742461783881997149 804018278423168955748931)
                      ·
                        rfl

theorem cell23_1565820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_1565820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565820 prefixEnd_1565820 := by exact prefixLift 1565820
  have htrace : WordTrace (prefixWord ++ tailWord_1565820) baseStart_1565820 baseEnd_1565820 := by
    simpa [prefixWord, tailWord_1565820, baseEnd_1565820] using wordTrace_append hprefix tailTrace_1565820
  have hstable : (prefixWord ++ tailWord_1565820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565820).length < 2 ^ (prefixWord ++ tailWord_1565820).sum := by decide
  have hdescent : baseEnd_1565820 < baseStart_1565820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565997 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1565997 : Nat := 118140960795 + 1565997 * 2 ^ 59
def prefixEnd_1565997 : Nat := 4983230072969 + 3 ^ 40 * 1565997 * 2
def baseEnd_1565997 : Nat := 804109164499014763235617

theorem tailTrace_1565997 : CollatzResearch.WordTrace tailWord_1565997 prefixEnd_1565997 804109164499014763235617 := by
  unfold tailWord_1565997
  simp only [CollatzResearch.WordTrace]
  refine ⟨57116602907667794839848245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38077735271778529893232163 57116602907667794839848245)
  ·
    refine ⟨5354681522593855766235773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57116602907667794839848245 5354681522593855766235773)
    ·
      refine ⟨2008005570972695912338415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5354681522593855766235773 2008005570972695912338415)
      ·
        refine ⟨3012008356459043868507623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008005570972695912338415 3012008356459043868507623)
        ·
          refine ⟨4518012534688565802761435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012008356459043868507623 4518012534688565802761435)
          ·
            refine ⟨6777018802032848704142153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518012534688565802761435 6777018802032848704142153)
            ·
              refine ⟨5082764101524636528106615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777018802032848704142153 5082764101524636528106615)
              ·
                refine ⟨7624146152286954792159923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082764101524636528106615 7624146152286954792159923)
                ·
                  refine ⟨11436219228430432188239885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7624146152286954792159923 11436219228430432188239885)
                  ·
                    refine ⟨4288582210661412070589957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11436219228430432188239885 4288582210661412070589957)
                    ·
                      refine ⟨804109164499014763235617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4288582210661412070589957 804109164499014763235617)
                      ·
                        rfl

theorem cell23_1565997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1565997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1565997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1565997 prefixEnd_1565997 := by exact prefixLift 1565997
  have htrace : WordTrace (prefixWord ++ tailWord_1565997) baseStart_1565997 baseEnd_1565997 := by
    simpa [prefixWord, tailWord_1565997, baseEnd_1565997] using wordTrace_append hprefix tailTrace_1565997
  have hstable : (prefixWord ++ tailWord_1565997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565997).length < 2 ^ (prefixWord ++ tailWord_1565997).sum := by decide
  have hdescent : baseEnd_1565997 < baseStart_1565997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566000 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_1566000 : Nat := 118140960795 + 1566000 * 2 ^ 59
def prefixEnd_1566000 : Nat := 4983230072969 + 3 ^ 40 * 1566000 * 2
def baseEnd_1566000 : Nat := 804110704940978251498103

theorem tailTrace_1566000 : CollatzResearch.WordTrace tailWord_1566000 prefixEnd_1566000 804110704940978251498103 := by
  unfold tailWord_1566000
  simp only [CollatzResearch.WordTrace]
  refine ⟨28558356163328463176103727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38077808217771284234804969 28558356163328463176103727)
  ·
    refine ⟨42837534244992694764155591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28558356163328463176103727 42837534244992694764155591)
    ·
      refine ⟨64256301367489042146233387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42837534244992694764155591 64256301367489042146233387)
      ·
        refine ⟨96384452051233563219350081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64256301367489042146233387 96384452051233563219350081)
        ·
          refine ⟨72288339038425172414512561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96384452051233563219350081 72288339038425172414512561)
          ·
            refine ⟨54216254278818879310884421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72288339038425172414512561 54216254278818879310884421)
            ·
              refine ⟨10165547677278539870790829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54216254278818879310884421 10165547677278539870790829)
              ·
                refine ⟨3812080378979452451546561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10165547677278539870790829 3812080378979452451546561)
                ·
                  refine ⟨2859060284234589338659921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812080378979452451546561 2859060284234589338659921)
                  ·
                    refine ⟨2144295213175942003994941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859060284234589338659921 2144295213175942003994941)
                    ·
                      refine ⟨804110704940978251498103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144295213175942003994941 804110704940978251498103)
                      ·
                        rfl

theorem cell23_1566000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_1566000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566000 prefixEnd_1566000 := by exact prefixLift 1566000
  have htrace : WordTrace (prefixWord ++ tailWord_1566000) baseStart_1566000 baseEnd_1566000 := by
    simpa [prefixWord, tailWord_1566000, baseEnd_1566000] using wordTrace_append hprefix tailTrace_1566000
  have hstable : (prefixWord ++ tailWord_1566000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566000).length < 2 ^ (prefixWord ++ tailWord_1566000).sum := by decide
  have hdescent : baseEnd_1566000 < baseStart_1566000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566003 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 8]
def baseStart_1566003 : Nat := 118140960795 + 1566003 * 2 ^ 59
def prefixEnd_1566003 : Nat := 4983230072969 + 3 ^ 40 * 1566003 * 2
def baseEnd_1566003 : Nat := 89345805042549082195621

theorem tailTrace_1566003 : CollatzResearch.WordTrace tailWord_1566003 prefixEnd_1566003 89345805042549082195621 := by
  unfold tailWord_1566003
  simp only [CollatzResearch.WordTrace]
  refine ⟨57116821745646057864566663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38077881163764038576377775 57116821745646057864566663)
  ·
    refine ⟨85675232618469086796849995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57116821745646057864566663 85675232618469086796849995)
    ·
      refine ⟨128512848927703630195274993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85675232618469086796849995 128512848927703630195274993)
      ·
        refine ⟨96384636695777722646456245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128512848927703630195274993 96384636695777722646456245)
        ·
          refine ⟨9036059690229161498105273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96384636695777722646456245 9036059690229161498105273)
          ·
            refine ⟨6777044767671871123578955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9036059690229161498105273 6777044767671871123578955)
            ·
              refine ⟨10165567151507806685368433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777044767671871123578955 10165567151507806685368433)
              ·
                refine ⟨7624175363630855014026325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10165567151507806685368433 7624175363630855014026325)
                ·
                  refine ⟨89345805042549082195621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7624175363630855014026325 89345805042549082195621)
                  ·
                    rfl

theorem cell23_1566003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 8].length) (baseStart_1566003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566003 prefixEnd_1566003 := by exact prefixLift 1566003
  have htrace : WordTrace (prefixWord ++ tailWord_1566003) baseStart_1566003 baseEnd_1566003 := by
    simpa [prefixWord, tailWord_1566003, baseEnd_1566003] using wordTrace_append hprefix tailTrace_1566003
  have hstable : (prefixWord ++ tailWord_1566003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566003).length < 2 ^ (prefixWord ++ tailWord_1566003).sum := by decide
  have hdescent : baseEnd_1566003 < baseStart_1566003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566017 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1566017 : Nat := 118140960795 + 1566017 * 2 ^ 59
def prefixEnd_1566017 : Nat := 4983230072969 + 3 ^ 40 * 1566017 * 2
def baseEnd_1566017 : Nat := 804119434112104684985525

theorem tailTrace_1566017 : CollatzResearch.WordTrace tailWord_1566017 prefixEnd_1566017 804119434112104684985525 := by
  unfold tailWord_1566017
  simp only [CollatzResearch.WordTrace]
  refine ⟨57117332367595338255576305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38078221578396892170384203 57117332367595338255576305)
  ·
    refine ⟨42837999275696503691682229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57117332367595338255576305 42837999275696503691682229)
    ·
      refine ⟨4016062432096547221095209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42837999275696503691682229 4016062432096547221095209)
      ·
        refine ⟨3012046824072410415821407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4016062432096547221095209 3012046824072410415821407)
        ·
          refine ⟨4518070236108615623732111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012046824072410415821407 4518070236108615623732111)
          ·
            refine ⟨6777105354162923435598167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518070236108615623732111 6777105354162923435598167)
            ·
              refine ⟨10165658031244385153397251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777105354162923435598167 10165658031244385153397251)
              ·
                refine ⟨15248487046866577730095877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165658031244385153397251 15248487046866577730095877)
                ·
                  refine ⟨2859091321287483324392977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15248487046866577730095877 2859091321287483324392977)
                  ·
                    refine ⟨2144318490965612493294733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859091321287483324392977 2144318490965612493294733)
                    ·
                      refine ⟨804119434112104684985525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144318490965612493294733 804119434112104684985525)
                      ·
                        rfl

theorem cell23_1566017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1566017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566017 prefixEnd_1566017 := by exact prefixLift 1566017
  have htrace : WordTrace (prefixWord ++ tailWord_1566017) baseStart_1566017 baseEnd_1566017 := by
    simpa [prefixWord, tailWord_1566017, baseEnd_1566017] using wordTrace_append hprefix tailTrace_1566017
  have hstable : (prefixWord ++ tailWord_1566017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566017).length < 2 ^ (prefixWord ++ tailWord_1566017).sum := by decide
  have hdescent : baseEnd_1566017 < baseStart_1566017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566037 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 6]
def baseStart_1566037 : Nat := 118140960795 + 1566037 * 2 ^ 59
def prefixEnd_1566037 : Nat := 4983230072969 + 3 ^ 40 * 1566037 * 2
def baseEnd_1566037 : Nat := 89347744858354956303937

theorem tailTrace_1566037 : CollatzResearch.WordTrace tailWord_1566037 prefixEnd_1566037 89347744858354956303937 := by
  unfold tailWord_1566037
  simp only [CollatzResearch.WordTrace]
  refine ⟨57118061827522881671304365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38078707885015254447536243 57118061827522881671304365)
  ·
    refine ⟨21419273185321080626739137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57118061827522881671304365 21419273185321080626739137)
    ·
      refine ⟨16064454888990810470054353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21419273185321080626739137 16064454888990810470054353)
      ·
        refine ⟨12048341166743107852540765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16064454888990810470054353 12048341166743107852540765)
        ·
          refine ⟨4518127937528665444702787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12048341166743107852540765 4518127937528665444702787)
          ·
            refine ⟨6777191906292998167054181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518127937528665444702787 6777191906292998167054181)
            ·
              refine ⟨1270723482429937156322659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6777191906292998167054181 1270723482429937156322659)
              ·
                refine ⟨1906085223644905734483989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270723482429937156322659 1906085223644905734483989)
                ·
                  refine ⟨89347744858354956303937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1906085223644905734483989 89347744858354956303937)
                  ·
                    rfl

theorem cell23_1566037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_1566037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566037 prefixEnd_1566037 := by exact prefixLift 1566037
  have htrace : WordTrace (prefixWord ++ tailWord_1566037) baseStart_1566037 baseEnd_1566037 := by
    simpa [prefixWord, tailWord_1566037, baseEnd_1566037] using wordTrace_append hprefix tailTrace_1566037
  have hstable : (prefixWord ++ tailWord_1566037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566037).length < 2 ^ (prefixWord ++ tailWord_1566037).sum := by decide
  have hdescent : baseEnd_1566037 < baseStart_1566037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566064 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 1, 1, 3]
def baseStart_1566064 : Nat := 118140960795 + 1566064 * 2 ^ 59
def prefixEnd_1566064 : Nat := 4983230072969 + 3 ^ 40 * 1566064 * 2
def baseEnd_1566064 : Nat := 804143567702866001097809

theorem tailTrace_1566064 : CollatzResearch.WordTrace tailWord_1566064 prefixEnd_1566064 804143567702866001097809 := by
  unfold tailWord_1566064
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559523299212532641268623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38079364398950043521691497 28559523299212532641268623)
  ·
    refine ⟨42839284948818798961902935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28559523299212532641268623 42839284948818798961902935)
    ·
      refine ⟨64258927423228198442854403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42839284948818798961902935 64258927423228198442854403)
      ·
        refine ⟨96388391134842297664281605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64258927423228198442854403 96388391134842297664281605)
        ·
          refine ⟨18072823337782930812052801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96388391134842297664281605 18072823337782930812052801)
          ·
            refine ⟨13554617503337198109039601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18072823337782930812052801 13554617503337198109039601)
            ·
              refine ⟨10165963127502898581779701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13554617503337198109039601 10165963127502898581779701)
              ·
                refine ⟨953059043203396742041847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10165963127502898581779701 953059043203396742041847)
                ·
                  refine ⟨1429588564805095113062771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953059043203396742041847 1429588564805095113062771)
                  ·
                    refine ⟨2144382847207642669594157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1429588564805095113062771 2144382847207642669594157)
                    ·
                      refine ⟨804143567702866001097809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144382847207642669594157 804143567702866001097809)
                      ·
                        rfl

theorem cell23_1566064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 1, 3].length) (baseStart_1566064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566064 prefixEnd_1566064 := by exact prefixLift 1566064
  have htrace : WordTrace (prefixWord ++ tailWord_1566064) baseStart_1566064 baseEnd_1566064 := by
    simpa [prefixWord, tailWord_1566064, baseEnd_1566064] using wordTrace_append hprefix tailTrace_1566064
  have hstable : (prefixWord ++ tailWord_1566064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566064).length < 2 ^ (prefixWord ++ tailWord_1566064).sum := by decide
  have hdescent : baseEnd_1566064 < baseStart_1566064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566080 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 4, 4]
def baseStart_1566080 : Nat := 118140960795 + 1566080 * 2 ^ 59
def prefixEnd_1566080 : Nat := 4983230072969 + 3 ^ 40 * 1566080 * 2
def baseEnd_1566080 : Nat := 268050594464445979499245

theorem tailTrace_1566080 : CollatzResearch.WordTrace tailWord_1566080 prefixEnd_1566080 268050594464445979499245 := by
  unfold tailWord_1566080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559815083183550007559847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38079753444244733343413129 28559815083183550007559847)
  ·
    refine ⟨42839722624775325011339771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28559815083183550007559847 42839722624775325011339771)
    ·
      refine ⟨64259583937162987517009657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42839722624775325011339771 64259583937162987517009657)
      ·
        refine ⟨48194687952872240637757243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64259583937162987517009657 48194687952872240637757243)
        ·
          refine ⟨72292031929308360956635865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48194687952872240637757243 72292031929308360956635865)
          ·
            refine ⟨54219023946981270717476899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72292031929308360956635865 54219023946981270717476899)
            ·
              refine ⟨81328535920471906076215349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54219023946981270717476899 81328535920471906076215349)
              ·
                refine ⟨7624550242544241194645189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81328535920471906076215349 7624550242544241194645189)
                ·
                  refine ⟨1429603170477045223995973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7624550242544241194645189 1429603170477045223995973)
                  ·
                    refine ⟨268050594464445979499245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429603170477045223995973 268050594464445979499245)
                    ·
                      rfl

theorem cell23_1566080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_1566080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566080 prefixEnd_1566080 := by exact prefixLift 1566080
  have htrace : WordTrace (prefixWord ++ tailWord_1566080) baseStart_1566080 baseEnd_1566080 := by
    simpa [prefixWord, tailWord_1566080, baseEnd_1566080] using wordTrace_append hprefix tailTrace_1566080
  have hstable : (prefixWord ++ tailWord_1566080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566080).length < 2 ^ (prefixWord ++ tailWord_1566080).sum := by decide
  have hdescent : baseEnd_1566080 < baseStart_1566080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566108 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1566108 : Nat := 118140960795 + 1566108 * 2 ^ 59
def prefixEnd_1566108 : Nat := 4983230072969 + 3 ^ 40 * 1566108 * 2
def baseEnd_1566108 : Nat := 804166160851663828947607

theorem tailTrace_1566108 : CollatzResearch.WordTrace tailWord_1566108 prefixEnd_1566108 804166160851663828947607 := by
  unfold tailWord_1566108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28560325705132830398569489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38080434273510440531425985 28560325705132830398569489)
  ·
    refine ⟨21420244278849622798927117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28560325705132830398569489 21420244278849622798927117)
    ·
      refine ⟨8032591604568608549597669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21420244278849622798927117 8032591604568608549597669)
      ·
        refine ⟨1506110925856614103049563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8032591604568608549597669 1506110925856614103049563)
        ·
          refine ⟨2259166388784921154574345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506110925856614103049563 2259166388784921154574345)
          ·
            refine ⟨1694374791588690865930759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259166388784921154574345 1694374791588690865930759)
            ·
              refine ⟨2541562187383036298896139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694374791588690865930759 2541562187383036298896139)
              ·
                refine ⟨3812343281074554448344209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541562187383036298896139 3812343281074554448344209)
                ·
                  refine ⟨2859257460805915836258157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812343281074554448344209 2859257460805915836258157)
                  ·
                    refine ⟨1072221547802218438596809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859257460805915836258157 1072221547802218438596809)
                    ·
                      refine ⟨804166160851663828947607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072221547802218438596809 804166160851663828947607)
                      ·
                        rfl

theorem cell23_1566108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1566108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566108 prefixEnd_1566108 := by exact prefixLift 1566108
  have htrace : WordTrace (prefixWord ++ tailWord_1566108) baseStart_1566108 baseEnd_1566108 := by
    simpa [prefixWord, tailWord_1566108, baseEnd_1566108] using wordTrace_append hprefix tailTrace_1566108
  have hstable : (prefixWord ++ tailWord_1566108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566108).length < 2 ^ (prefixWord ++ tailWord_1566108).sum := by decide
  have hdescent : baseEnd_1566108 < baseStart_1566108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566124 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 3]
def baseStart_1566124 : Nat := 118140960795 + 1566124 * 2 ^ 59
def prefixEnd_1566124 : Nat := 4983230072969 + 3 ^ 40 * 1566124 * 2
def baseEnd_1566124 : Nat := 804174376542135766347533

theorem tailTrace_1566124 : CollatzResearch.WordTrace tailWord_1566124 prefixEnd_1566124 804174376542135766347533 := by
  unfold tailWord_1566124
  simp only [CollatzResearch.WordTrace]
  refine ⟨28560617489103847764860713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38080823318805130353147617 28560617489103847764860713)
  ·
    refine ⟨21420463116827885823645535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28560617489103847764860713 21420463116827885823645535)
    ·
      refine ⟨32130694675241828735468303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21420463116827885823645535 32130694675241828735468303)
      ·
        refine ⟨48196042012862743103202455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32130694675241828735468303 48196042012862743103202455)
        ·
          refine ⟨72294063019294114654803683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48196042012862743103202455 72294063019294114654803683)
          ·
            refine ⟨108441094528941171982205525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72294063019294114654803683 108441094528941171982205525)
            ·
              refine ⟨1270794076511029359166471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 108441094528941171982205525 1270794076511029359166471)
              ·
                refine ⟨1906191114766544038749707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270794076511029359166471 1906191114766544038749707)
                ·
                  refine ⟨2859286672149816058124561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906191114766544038749707 2859286672149816058124561)
                  ·
                    refine ⟨2144465004112362043593421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859286672149816058124561 2144465004112362043593421)
                    ·
                      refine ⟨804174376542135766347533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144465004112362043593421 804174376542135766347533)
                      ·
                        rfl

theorem cell23_1566124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_1566124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566124 prefixEnd_1566124 := by exact prefixLift 1566124
  have htrace : WordTrace (prefixWord ++ tailWord_1566124) baseStart_1566124 baseEnd_1566124 := by
    simpa [prefixWord, tailWord_1566124, baseEnd_1566124] using wordTrace_append hprefix tailTrace_1566124
  have hstable : (prefixWord ++ tailWord_1566124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566124).length < 2 ^ (prefixWord ++ tailWord_1566124).sum := by decide
  have hdescent : baseEnd_1566124 < baseStart_1566124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566147 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 5, 3, 2]
def baseStart_1566147 : Nat := 118140960795 + 1566147 * 2 ^ 59
def prefixEnd_1566147 : Nat := 4983230072969 + 3 ^ 40 * 1566147 * 2
def baseEnd_1566147 : Nat := 804186186597189176359927

theorem tailTrace_1566147 : CollatzResearch.WordTrace tailWord_1566147 prefixEnd_1566147 804186186597189176359927 := by
  unfold tailWord_1566147
  simp only [CollatzResearch.WordTrace]
  refine ⟨57122073857124370457808695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38081382571416246971872463 57122073857124370457808695)
  ·
    refine ⟨85683110785686555686713043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57122073857124370457808695 85683110785686555686713043)
    ·
      refine ⟨128524666178529833530069565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85683110785686555686713043 128524666178529833530069565)
      ·
        refine ⟨48196749816948687573776087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128524666178529833530069565 48196749816948687573776087)
        ·
          refine ⟨72295124725423031360664131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48196749816948687573776087 72295124725423031360664131)
          ·
            refine ⟨108442687088134547040996197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72295124725423031360664131 108442687088134547040996197)
            ·
              refine ⟨20333003829025227570186787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108442687088134547040996197 20333003829025227570186787)
              ·
                refine ⟨30499505743537841355280181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20333003829025227570186787 30499505743537841355280181)
                ·
                  refine ⟨2859328663456672627057517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30499505743537841355280181 2859328663456672627057517)
                  ·
                    refine ⟨1072248248796252235146569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859328663456672627057517 1072248248796252235146569)
                    ·
                      refine ⟨804186186597189176359927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072248248796252235146569 804186186597189176359927)
                      ·
                        rfl

theorem cell23_1566147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_1566147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566147 prefixEnd_1566147 := by exact prefixLift 1566147
  have htrace : WordTrace (prefixWord ++ tailWord_1566147) baseStart_1566147 baseEnd_1566147 := by
    simpa [prefixWord, tailWord_1566147, baseEnd_1566147] using wordTrace_append hprefix tailTrace_1566147
  have hstable : (prefixWord ++ tailWord_1566147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566147).length < 2 ^ (prefixWord ++ tailWord_1566147).sum := by decide
  have hdescent : baseEnd_1566147 < baseStart_1566147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566154 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_1566154 : Nat := 118140960795 + 1566154 * 2 ^ 59
def prefixEnd_1566154 : Nat := 4983230072969 + 3 ^ 40 * 1566154 * 2
def baseEnd_1566154 : Nat := 804189780961770648972395

theorem tailTrace_1566154 : CollatzResearch.WordTrace tailWord_1566154 prefixEnd_1566154 804189780961770648972395 := by
  unfold tailWord_1566154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280582292024752663328379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38081552778732673768875677 14280582292024752663328379)
  ·
    refine ⟨21420873438037128994992569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14280582292024752663328379 21420873438037128994992569)
    ·
      refine ⟨16065655078527846746244427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21420873438037128994992569 16065655078527846746244427)
      ·
        refine ⟨24098482617791770119366641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16065655078527846746244427 24098482617791770119366641)
        ·
          refine ⟨18073861963343827589524981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24098482617791770119366641 18073861963343827589524981)
          ·
            refine ⟨1694424559063483836517967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18073861963343827589524981 1694424559063483836517967)
            ·
              refine ⟨2541636838595225754776951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694424559063483836517967 2541636838595225754776951)
              ·
                refine ⟨3812455257892838632165427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541636838595225754776951 3812455257892838632165427)
                ·
                  refine ⟨5718682886839257948248141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812455257892838632165427 5718682886839257948248141)
                  ·
                    refine ⟨2144506082564721730593053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5718682886839257948248141 2144506082564721730593053)
                    ·
                      refine ⟨804189780961770648972395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144506082564721730593053 804189780961770648972395)
                      ·
                        rfl

theorem cell23_1566154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_1566154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566154 prefixEnd_1566154 := by exact prefixLift 1566154
  have htrace : WordTrace (prefixWord ++ tailWord_1566154) baseStart_1566154 baseEnd_1566154 := by
    simpa [prefixWord, tailWord_1566154, baseEnd_1566154] using wordTrace_append hprefix tailTrace_1566154
  have hstable : (prefixWord ++ tailWord_1566154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566154).length < 2 ^ (prefixWord ++ tailWord_1566154).sum := by decide
  have hdescent : baseEnd_1566154 < baseStart_1566154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566181 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1566181 : Nat := 118140960795 + 1566181 * 2 ^ 59
def prefixEnd_1566181 : Nat := 4983230072969 + 3 ^ 40 * 1566181 * 2
def baseEnd_1566181 : Nat := 804203644939442043334771

theorem tailTrace_1566181 : CollatzResearch.WordTrace tailWord_1566181 prefixEnd_1566181 804203644939442043334771 := by
  unfold tailWord_1566181
  simp only [CollatzResearch.WordTrace]
  refine ⟨57123313939001194264546397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38082209292667462843030931 57123313939001194264546397)
  ·
    refine ⟨21421242727125447849204899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57123313939001194264546397 21421242727125447849204899)
    ·
      refine ⟨32131864090688171773807349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421242727125447849204899 32131864090688171773807349)
      ·
        refine ⟨3012362258502016103794439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32131864090688171773807349 3012362258502016103794439)
        ·
          refine ⟨4518543387753024155691659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012362258502016103794439 4518543387753024155691659)
          ·
            refine ⟨6777815081629536233537489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518543387753024155691659 6777815081629536233537489)
            ·
              refine ⟨5083361311222152175153117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777815081629536233537489 5083361311222152175153117)
              ·
                refine ⟨1906260491708307065682419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5083361311222152175153117 1906260491708307065682419)
                ·
                  refine ⟨2859390737562460598523629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906260491708307065682419 2859390737562460598523629)
                  ·
                    refine ⟨1072271526585922724446361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859390737562460598523629 1072271526585922724446361)
                    ·
                      refine ⟨804203644939442043334771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072271526585922724446361 804203644939442043334771)
                      ·
                        rfl

theorem cell23_1566181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1566181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566181 prefixEnd_1566181 := by exact prefixLift 1566181
  have htrace : WordTrace (prefixWord ++ tailWord_1566181) baseStart_1566181 baseEnd_1566181 := by
    simpa [prefixWord, tailWord_1566181, baseEnd_1566181] using wordTrace_append hprefix tailTrace_1566181
  have hstable : (prefixWord ++ tailWord_1566181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566181).length < 2 ^ (prefixWord ++ tailWord_1566181).sum := by decide
  have hdescent : baseEnd_1566181 < baseStart_1566181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566228 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1566228 : Nat := 118140960795 + 1566228 * 2 ^ 59
def prefixEnd_1566228 : Nat := 4983230072969 + 3 ^ 40 * 1566228 * 2
def baseEnd_1566228 : Nat := 804227778530203359447055

theorem tailTrace_1566228 : CollatzResearch.WordTrace tailWord_1566228 prefixEnd_1566228 804227778530203359447055 := by
  unfold tailWord_1566228
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562514084915460645753669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38083352113220614194338225 28562514084915460645753669)
  ·
    refine ⟨5355471390921648871078813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28562514084915460645753669 5355471390921648871078813)
    ·
      refine ⟨2008301771595618326654555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5355471390921648871078813 2008301771595618326654555)
      ·
        refine ⟨3012452657393427489981833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008301771595618326654555 3012452657393427489981833)
        ·
          refine ⟨2259339493045070617486375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3012452657393427489981833 2259339493045070617486375)
          ·
            refine ⟨3389009239567605926229563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259339493045070617486375 3389009239567605926229563)
            ·
              refine ⟨5083513859351408889344345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389009239567605926229563 5083513859351408889344345)
              ·
                refine ⟨3812635394513556667008259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5083513859351408889344345 3812635394513556667008259)
                ·
                  refine ⟨5718953091770335000512389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812635394513556667008259 5718953091770335000512389)
                  ·
                    refine ⟨1072303704706937812596073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718953091770335000512389 1072303704706937812596073)
                    ·
                      refine ⟨804227778530203359447055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072303704706937812596073 804227778530203359447055)
                      ·
                        rfl

theorem cell23_1566228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1566228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566228 prefixEnd_1566228 := by exact prefixLift 1566228
  have htrace : WordTrace (prefixWord ++ tailWord_1566228) baseStart_1566228 baseEnd_1566228 := by
    simpa [prefixWord, tailWord_1566228, baseEnd_1566228] using wordTrace_append hprefix tailTrace_1566228
  have hstable : (prefixWord ++ tailWord_1566228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566228).length < 2 ^ (prefixWord ++ tailWord_1566228).sum := by decide
  have hdescent : baseEnd_1566228 < baseStart_1566228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566284 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1566284 : Nat := 118140960795 + 1566284 * 2 ^ 59
def prefixEnd_1566284 : Nat := 4983230072969 + 3 ^ 40 * 1566284 * 2
def baseEnd_1566284 : Nat := 804256533446855140346797

theorem tailTrace_1566284 : CollatzResearch.WordTrace tailWord_1566284 prefixEnd_1566284 804256533446855140346797 := by
  unfold tailWord_1566284
  simp only [CollatzResearch.WordTrace]
  refine ⟨28563535328814021427772953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38084713771752028570363937 28563535328814021427772953)
  ·
    refine ⟨21422651496610516070829715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28563535328814021427772953 21422651496610516070829715)
    ·
      refine ⟨32133977244915774106244573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21422651496610516070829715 32133977244915774106244573)
      ·
        refine ⟨12050241466843415289841715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32133977244915774106244573 12050241466843415289841715)
        ·
          refine ⟨18075362200265122934762573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12050241466843415289841715 18075362200265122934762573)
          ·
            refine ⟨6778260825099421100535965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18075362200265122934762573 6778260825099421100535965)
            ·
              refine ⟨2541847809412282912700987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6778260825099421100535965 2541847809412282912700987)
              ·
                refine ⟨3812771714118424369051481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541847809412282912700987 3812771714118424369051481)
                ·
                  refine ⟨2859578785588818276788611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3812771714118424369051481 2859578785588818276788611)
                  ·
                    refine ⟨4289368178383227415182917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2859578785588818276788611 4289368178383227415182917)
                    ·
                      refine ⟨804256533446855140346797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4289368178383227415182917 804256533446855140346797)
                      ·
                        rfl

theorem cell23_1566284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1566284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566284 prefixEnd_1566284 := by exact prefixLift 1566284
  have htrace : WordTrace (prefixWord ++ tailWord_1566284) baseStart_1566284 baseEnd_1566284 := by
    simpa [prefixWord, tailWord_1566284, baseEnd_1566284] using wordTrace_append hprefix tailTrace_1566284
  have hstable : (prefixWord ++ tailWord_1566284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566284).length < 2 ^ (prefixWord ++ tailWord_1566284).sum := by decide
  have hdescent : baseEnd_1566284 < baseStart_1566284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566307 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 8]
def baseStart_1566307 : Nat := 118140960795 + 1566307 * 2 ^ 59
def prefixEnd_1566307 : Nat := 4983230072969 + 3 ^ 40 * 1566307 * 2
def baseEnd_1566307 : Nat := 89363149277989838928799

theorem tailTrace_1566307 : CollatzResearch.WordTrace tailWord_1566307 prefixEnd_1566307 89363149277989838928799 := by
  unfold tailWord_1566307
  simp only [CollatzResearch.WordTrace]
  refine ⟨57127909536544717783633175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38085273024363145189088783 57127909536544717783633175)
  ·
    refine ⟨85691864304817076675449763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57127909536544717783633175 85691864304817076675449763)
    ·
      refine ⟨128537796457225615013174645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85691864304817076675449763 128537796457225615013174645)
      ·
        refine ⟨12050418417864901407485123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128537796457225615013174645 12050418417864901407485123)
        ·
          refine ⟨18075627626797352111227685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12050418417864901407485123 18075627626797352111227685)
          ·
            refine ⟨3389180180024503520855191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18075627626797352111227685 3389180180024503520855191)
            ·
              refine ⟨5083770270036755281282787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389180180024503520855191 5083770270036755281282787)
              ·
                refine ⟨7625655405055132921924181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083770270036755281282787 7625655405055132921924181)
                ·
                  refine ⟨89363149277989838928799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7625655405055132921924181 89363149277989838928799)
                  ·
                    rfl

theorem cell23_1566307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 8].length) (baseStart_1566307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566307 prefixEnd_1566307 := by exact prefixLift 1566307
  have htrace : WordTrace (prefixWord ++ tailWord_1566307) baseStart_1566307 baseEnd_1566307 := by
    simpa [prefixWord, tailWord_1566307, baseEnd_1566307] using wordTrace_append hprefix tailTrace_1566307
  have hstable : (prefixWord ++ tailWord_1566307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566307).length < 2 ^ (prefixWord ++ tailWord_1566307).sum := by decide
  have hdescent : baseEnd_1566307 < baseStart_1566307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566311 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 1, 4]
def baseStart_1566311 : Nat := 118140960795 + 1566311 * 2 ^ 59
def prefixEnd_1566311 : Nat := 4983230072969 + 3 ^ 40 * 1566311 * 2
def baseEnd_1566311 : Nat := 268090132474842178236391

theorem tailTrace_1566311 : CollatzResearch.WordTrace tailWord_1566311 prefixEnd_1566311 268090132474842178236391 := by
  unfold tailWord_1566311
  simp only [CollatzResearch.WordTrace]
  refine ⟨57128055428530226466778787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38085370285686817644519191 57128055428530226466778787)
  ·
    refine ⟨85692083142795339700168181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57128055428530226466778787 85692083142795339700168181)
    ·
      refine ⟨8033632794637063096890767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85692083142795339700168181 8033632794637063096890767)
      ·
        refine ⟨12050449191955594645336151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033632794637063096890767 12050449191955594645336151)
        ·
          refine ⟨18075673787933391968004227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12050449191955594645336151 18075673787933391968004227)
          ·
            refine ⟨27113510681900087952006341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18075673787933391968004227 27113510681900087952006341)
            ·
              refine ⟨5083783252856266491001189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27113510681900087952006341 5083783252856266491001189)
              ·
                refine ⟨953209359910549967062723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5083783252856266491001189 953209359910549967062723)
                ·
                  refine ⟨1429814039865824950594085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953209359910549967062723 1429814039865824950594085)
                  ·
                    refine ⟨268090132474842178236391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429814039865824950594085 268090132474842178236391)
                    ·
                      rfl

theorem cell23_1566311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_1566311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566311 prefixEnd_1566311 := by exact prefixLift 1566311
  have htrace : WordTrace (prefixWord ++ tailWord_1566311) baseStart_1566311 baseEnd_1566311 := by
    simpa [prefixWord, tailWord_1566311, baseEnd_1566311] using wordTrace_append hprefix tailTrace_1566311
  have hstable : (prefixWord ++ tailWord_1566311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566311).length < 2 ^ (prefixWord ++ tailWord_1566311).sum := by decide
  have hdescent : baseEnd_1566311 < baseStart_1566311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566368 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1566368 : Nat := 118140960795 + 1566368 * 2 ^ 59
def prefixEnd_1566368 : Nat := 4983230072969 + 3 ^ 40 * 1566368 * 2
def baseEnd_1566368 : Nat := 804299665821832811696411

theorem tailTrace_1566368 : CollatzResearch.WordTrace tailWord_1566368 prefixEnd_1566368 804299665821832811696411 := by
  unfold tailWord_1566368
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565067194661862600801879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38086756259549150134402505 28565067194661862600801879)
  ·
    refine ⟨42847600791992793901202819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28565067194661862600801879 42847600791992793901202819)
    ·
      refine ⟨64271401187989190851804229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42847600791992793901202819 64271401187989190851804229)
      ·
        refine ⟨12050887722747973284713293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64271401187989190851804229 12050887722747973284713293)
        ·
          refine ⟨4519082896030489981767485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12050887722747973284713293 4519082896030489981767485)
          ·
            refine ⟨1694656086011433743162807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4519082896030489981767485 1694656086011433743162807)
            ·
              refine ⟨2541984129017150614744211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694656086011433743162807 2541984129017150614744211)
              ·
                refine ⟨3812976193525725922116317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541984129017150614744211 3812976193525725922116317)
                ·
                  refine ⟨1429866072572147220793619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3812976193525725922116317 1429866072572147220793619)
                  ·
                    refine ⟨2144799108858220831190429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1429866072572147220793619 2144799108858220831190429)
                    ·
                      refine ⟨804299665821832811696411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144799108858220831190429 804299665821832811696411)
                      ·
                        rfl

theorem cell23_1566368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1566368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566368 prefixEnd_1566368 := by exact prefixLift 1566368
  have htrace : WordTrace (prefixWord ++ tailWord_1566368) baseStart_1566368 baseEnd_1566368 := by
    simpa [prefixWord, tailWord_1566368, baseEnd_1566368] using wordTrace_append hprefix tailTrace_1566368
  have hstable : (prefixWord ++ tailWord_1566368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566368).length < 2 ^ (prefixWord ++ tailWord_1566368).sum := by decide
  have hdescent : baseEnd_1566368 < baseStart_1566368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566387 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6]
def baseStart_1566387 : Nat := 118140960795 + 1566387 * 2 ^ 59
def prefixEnd_1566387 : Nat := 4983230072969 + 3 ^ 40 * 1566387 * 2
def baseEnd_1566387 : Nat := 804309421954268237358823

theorem tailTrace_1566387 : CollatzResearch.WordTrace tailWord_1566387 prefixEnd_1566387 804309421954268237358823 := by
  unfold tailWord_1566387
  simp only [CollatzResearch.WordTrace]
  refine ⟨57130827376254891446545415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38087218250836594297696943 57130827376254891446545415)
  ·
    refine ⟨85696241064382337169818123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57130827376254891446545415 85696241064382337169818123)
    ·
      refine ⟨128544361596573505754727185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85696241064382337169818123 128544361596573505754727185)
      ·
        refine ⟨96408271197430129316045389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128544361596573505754727185 96408271197430129316045389)
        ·
          refine ⟨36153101699036298493517021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96408271197430129316045389 36153101699036298493517021)
          ·
            refine ⟨13557413137138611935068883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36153101699036298493517021 13557413137138611935068883)
            ·
              refine ⟨20336119705707917902603325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13557413137138611935068883 20336119705707917902603325)
              ·
                refine ⟨7626044889640469213476247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20336119705707917902603325 7626044889640469213476247)
                ·
                  refine ⟨11439067334460703820214371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7626044889640469213476247 11439067334460703820214371)
                  ·
                    refine ⟨17158601001691055730321557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11439067334460703820214371 17158601001691055730321557)
                    ·
                      refine ⟨804309421954268237358823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17158601001691055730321557 804309421954268237358823)
                      ·
                        rfl

theorem cell23_1566387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_1566387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566387 prefixEnd_1566387 := by exact prefixLift 1566387
  have htrace : WordTrace (prefixWord ++ tailWord_1566387) baseStart_1566387 baseEnd_1566387 := by
    simpa [prefixWord, tailWord_1566387, baseEnd_1566387] using wordTrace_append hprefix tailTrace_1566387
  have hstable : (prefixWord ++ tailWord_1566387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566387).length < 2 ^ (prefixWord ++ tailWord_1566387).sum := by decide
  have hdescent : baseEnd_1566387 < baseStart_1566387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566391 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_1566391 : Nat := 118140960795 + 1566391 * 2 ^ 59
def prefixEnd_1566391 : Nat := 4983230072969 + 3 ^ 40 * 1566391 * 2
def baseEnd_1566391 : Nat := 804311475876886221708805

theorem tailTrace_1566391 : CollatzResearch.WordTrace tailWord_1566391 prefixEnd_1566391 804311475876886221708805 := by
  unfold tailWord_1566391
  simp only [CollatzResearch.WordTrace]
  refine ⟨57130973268240400129691027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38087315512160266753127351 57130973268240400129691027)
  ·
    refine ⟨85696459902360600194536541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57130973268240400129691027 85696459902360600194536541)
    ·
      refine ⟨32136172463385225072951203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85696459902360600194536541 32136172463385225072951203)
      ·
        refine ⟨48204258695077837609426805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32136172463385225072951203 48204258695077837609426805)
        ·
          refine ⟨4519149252663547275883763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48204258695077837609426805 4519149252663547275883763)
          ·
            refine ⟨6778723878995320913825645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519149252663547275883763 6778723878995320913825645)
            ·
              refine ⟨2542021454623245342684617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6778723878995320913825645 2542021454623245342684617)
              ·
                refine ⟨1906516090967434007013463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542021454623245342684617 1906516090967434007013463)
                ·
                  refine ⟨2859774136451151010520195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906516090967434007013463 2859774136451151010520195)
                  ·
                    refine ⟨4289661204676726515780293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2859774136451151010520195 4289661204676726515780293)
                    ·
                      refine ⟨804311475876886221708805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4289661204676726515780293 804311475876886221708805)
                      ·
                        rfl

theorem cell23_1566391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_1566391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566391 prefixEnd_1566391 := by exact prefixLift 1566391
  have htrace : WordTrace (prefixWord ++ tailWord_1566391) baseStart_1566391 baseEnd_1566391 := by
    simpa [prefixWord, tailWord_1566391, baseEnd_1566391] using wordTrace_append hprefix tailTrace_1566391
  have hstable : (prefixWord ++ tailWord_1566391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566391).length < 2 ^ (prefixWord ++ tailWord_1566391).sum := by decide
  have hdescent : baseEnd_1566391 < baseStart_1566391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566397 : List Nat := [1, 4, 1, 2, 1, 2, 1, 11]
def baseStart_1566397 : Nat := 118140960795 + 1566397 * 2 ^ 59
def prefixEnd_1566397 : Nat := 4983230072969 + 3 ^ 40 * 1566397 * 2
def baseEnd_1566397 : Nat := 29789428028178266601251

theorem tailTrace_1566397 : CollatzResearch.WordTrace tailWord_1566397 prefixEnd_1566397 29789428028178266601251 := by
  unfold tailWord_1566397
  simp only [CollatzResearch.WordTrace]
  refine ⟨57131192106218663154409445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38087461404145775436272963 57131192106218663154409445)
  ·
    refine ⟨10712098519915999341451771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57131192106218663154409445 10712098519915999341451771)
    ·
      refine ⟨16068147779873999012177657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10712098519915999341451771 16068147779873999012177657)
      ·
        refine ⟨12051110834905499259133243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16068147779873999012177657 12051110834905499259133243)
        ·
          refine ⟨18076666252358248888699865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12051110834905499259133243 18076666252358248888699865)
          ·
            refine ⟨13557499689268686666524899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18076666252358248888699865 13557499689268686666524899)
            ·
              refine ⟨20336249533903029999787349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13557499689268686666524899 20336249533903029999787349)
              ·
                refine ⟨29789428028178266601251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 20336249533903029999787349 29789428028178266601251)
                ·
                  rfl

theorem cell23_1566397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 11].length) (baseStart_1566397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566397 prefixEnd_1566397 := by exact prefixLift 1566397
  have htrace : WordTrace (prefixWord ++ tailWord_1566397) baseStart_1566397 baseEnd_1566397 := by
    simpa [prefixWord, tailWord_1566397, baseEnd_1566397] using wordTrace_append hprefix tailTrace_1566397
  have hstable : (prefixWord ++ tailWord_1566397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566397).length < 2 ^ (prefixWord ++ tailWord_1566397).sum := by decide
  have hdescent : baseEnd_1566397 < baseStart_1566397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566418 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1566418 : Nat := 118140960795 + 1566418 * 2 ^ 59
def prefixEnd_1566418 : Nat := 4983230072969 + 3 ^ 40 * 1566418 * 2
def baseEnd_1566418 : Nat := 268108446618185872023727

theorem tailTrace_1566418 : CollatzResearch.WordTrace tailWord_1566418 prefixEnd_1566418 268108446618185872023727 := by
  unfold tailWord_1566418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14282989509785645935230977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38087972026095055827282605 14282989509785645935230977)
  ·
    refine ⟨10712242132339234451423233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14282989509785645935230977 10712242132339234451423233)
    ·
      refine ⟨8034181599254425838567425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10712242132339234451423233 8034181599254425838567425)
      ·
        refine ⟨6025636199440819378925569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8034181599254425838567425 6025636199440819378925569)
        ·
          refine ⟨4519227149580614534194177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025636199440819378925569 4519227149580614534194177)
          ·
            refine ⟨3389420362185460900645633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4519227149580614534194177 3389420362185460900645633)
            ·
              refine ⟨2542065271639095675484225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389420362185460900645633 2542065271639095675484225)
              ·
                refine ⟨1906548953729321756613169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542065271639095675484225 1906548953729321756613169)
                ·
                  refine ⟨1429911715296991317459877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1906548953729321756613169 1429911715296991317459877)
                  ·
                    refine ⟨268108446618185872023727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429911715296991317459877 268108446618185872023727)
                    ·
                      rfl

theorem cell23_1566418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1566418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566418 prefixEnd_1566418 := by exact prefixLift 1566418
  have htrace : WordTrace (prefixWord ++ tailWord_1566418) baseStart_1566418 baseEnd_1566418 := by
    simpa [prefixWord, tailWord_1566418, baseEnd_1566418] using wordTrace_append hprefix tailTrace_1566418
  have hstable : (prefixWord ++ tailWord_1566418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566418).length < 2 ^ (prefixWord ++ tailWord_1566418).sum := by decide
  have hdescent : baseEnd_1566418 < baseStart_1566418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566424 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1566424 : Nat := 118140960795 + 1566424 * 2 ^ 59
def prefixEnd_1566424 : Nat := 4983230072969 + 3 ^ 40 * 1566424 * 2
def baseEnd_1566424 : Nat := 804328420738484592596153

theorem tailTrace_1566424 : CollatzResearch.WordTrace tailWord_1566424 prefixEnd_1566424 804328420738484592596153 := by
  unfold tailWord_1566424
  simp only [CollatzResearch.WordTrace]
  refine ⟨28566088438560423382821163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38088117918080564510428217 28566088438560423382821163)
  ·
    refine ⟨42849132657840635074231745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28566088438560423382821163 42849132657840635074231745)
    ·
      refine ⟨32136849493380476305673809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42849132657840635074231745 32136849493380476305673809)
      ·
        refine ⟨24102637120035357229255357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32136849493380476305673809 24102637120035357229255357)
        ·
          refine ⟨9038488920013258960970759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24102637120035357229255357 9038488920013258960970759)
          ·
            refine ⟨13557733380019888441456139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038488920013258960970759 13557733380019888441456139)
            ·
              refine ⟨20336600070029832662184209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13557733380019888441456139 20336600070029832662184209)
              ·
                refine ⟨15252450052522374496638157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20336600070029832662184209 15252450052522374496638157)
                ·
                  refine ⟨5719668769695890436239309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15252450052522374496638157 5719668769695890436239309)
                  ·
                    refine ⟨2144875788635958913589741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5719668769695890436239309 2144875788635958913589741)
                    ·
                      refine ⟨804328420738484592596153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144875788635958913589741 804328420738484592596153)
                      ·
                        rfl

theorem cell23_1566424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1566424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566424 prefixEnd_1566424 := by exact prefixLift 1566424
  have htrace : WordTrace (prefixWord ++ tailWord_1566424) baseStart_1566424 baseEnd_1566424 := by
    simpa [prefixWord, tailWord_1566424, baseEnd_1566424] using wordTrace_append hprefix tailTrace_1566424
  have hstable : (prefixWord ++ tailWord_1566424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566424).length < 2 ^ (prefixWord ++ tailWord_1566424).sum := by decide
  have hdescent : baseEnd_1566424 < baseStart_1566424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566425 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 1, 2, 2]
def baseStart_1566425 : Nat := 118140960795 + 1566425 * 2 ^ 59
def prefixEnd_1566425 : Nat := 4983230072969 + 3 ^ 40 * 1566425 * 2
def baseEnd_1566425 : Nat := 804328934219139088683649

theorem tailTrace_1566425 : CollatzResearch.WordTrace tailWord_1566425 prefixEnd_1566425 804328934219139088683649 := by
  unfold tailWord_1566425
  simp only [CollatzResearch.WordTrace]
  refine ⟨57132213350117223936428729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38088142233411482624285819 57132213350117223936428729)
  ·
    refine ⟨42849160012587917952321547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57132213350117223936428729 42849160012587917952321547)
    ·
      refine ⟨64273740018881876928482321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42849160012587917952321547 64273740018881876928482321)
      ·
        refine ⟨48205305014161407696361741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64273740018881876928482321 48205305014161407696361741)
        ·
          refine ⟨18076989380310527886135653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48205305014161407696361741 18076989380310527886135653)
          ·
            refine ⟨3389435508808223978650435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18076989380310527886135653 3389435508808223978650435)
            ·
              refine ⟨5084153263212335967975653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389435508808223978650435 5084153263212335967975653)
              ·
                refine ⟨953278736852312993995435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5084153263212335967975653 953278736852312993995435)
                ·
                  refine ⟨1429918105278469490993153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953278736852312993995435 1429918105278469490993153)
                  ·
                    refine ⟨1072438578958852118244865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1429918105278469490993153 1072438578958852118244865)
                    ·
                      refine ⟨804328934219139088683649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072438578958852118244865 804328934219139088683649)
                      ·
                        rfl

theorem cell23_1566425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_1566425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566425 prefixEnd_1566425 := by exact prefixLift 1566425
  have htrace : WordTrace (prefixWord ++ tailWord_1566425) baseStart_1566425 baseEnd_1566425 := by
    simpa [prefixWord, tailWord_1566425, baseEnd_1566425] using wordTrace_append hprefix tailTrace_1566425
  have hstable : (prefixWord ++ tailWord_1566425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566425).length < 2 ^ (prefixWord ++ tailWord_1566425).sum := by decide
  have hdescent : baseEnd_1566425 < baseStart_1566425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566451 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 3, 3, 2]
def baseStart_1566451 : Nat := 118140960795 + 1566451 * 2 ^ 59
def prefixEnd_1566451 : Nat := 4983230072969 + 3 ^ 40 * 1566451 * 2
def baseEnd_1566451 : Nat := 804342284716155986958529

theorem tailTrace_1566451 : CollatzResearch.WordTrace tailWord_1566451 prefixEnd_1566451 804342284716155986958529 := by
  unfold tailWord_1566451
  simp only [CollatzResearch.WordTrace]
  refine ⟨57133161648023030376875207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38088774432015353584583471 57133161648023030376875207)
  ·
    refine ⟨85699742472034545565312811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57133161648023030376875207 85699742472034545565312811)
    ·
      refine ⟨128549613708051818347969217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85699742472034545565312811 128549613708051818347969217)
      ·
        refine ⟨96412210281038863760976913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128549613708051818347969217 96412210281038863760976913)
        ·
          refine ⟨72309157710779147820732685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96412210281038863760976913 72309157710779147820732685)
          ·
            refine ⟨27115934141542180432774757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72309157710779147820732685 27115934141542180432774757)
            ·
              refine ⟨5084237651539158831145267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27115934141542180432774757 5084237651539158831145267)
              ·
                refine ⟨7626356477308738246717901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084237651539158831145267 7626356477308738246717901)
                ·
                  refine ⟨2859883678990776842519213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7626356477308738246717901 2859883678990776842519213)
                  ·
                    refine ⟨1072456379621541315944705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859883678990776842519213 1072456379621541315944705)
                    ·
                      refine ⟨804342284716155986958529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072456379621541315944705 804342284716155986958529)
                      ·
                        rfl

theorem cell23_1566451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3, 2].length) (baseStart_1566451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566451 prefixEnd_1566451 := by exact prefixLift 1566451
  have htrace : WordTrace (prefixWord ++ tailWord_1566451) baseStart_1566451 baseEnd_1566451 := by
    simpa [prefixWord, tailWord_1566451, baseEnd_1566451] using wordTrace_append hprefix tailTrace_1566451
  have hstable : (prefixWord ++ tailWord_1566451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566451).length < 2 ^ (prefixWord ++ tailWord_1566451).sum := by decide
  have hdescent : baseEnd_1566451 < baseStart_1566451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566462 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1566462 : Nat := 118140960795 + 1566462 * 2 ^ 59
def prefixEnd_1566462 : Nat := 4983230072969 + 3 ^ 40 * 1566462 * 2
def baseEnd_1566462 : Nat := 804347933003355443920979

theorem tailTrace_1566462 : CollatzResearch.WordTrace tailWord_1566462 prefixEnd_1566462 804347933003355443920979 := by
  unfold tailWord_1566462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7141695356372897406940705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38089041900655452837017093 7141695356372897406940705)
  ·
    refine ⟨5356271517279673055205529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7141695356372897406940705 5356271517279673055205529)
    ·
      refine ⟨4017203637959754791404147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5356271517279673055205529 4017203637959754791404147)
      ·
        refine ⟨6025805456939632187106221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017203637959754791404147 6025805456939632187106221)
        ·
          refine ⟨2259677046352362070164833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6025805456939632187106221 2259677046352362070164833)
          ·
            refine ⟨1694757784764271552623625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259677046352362070164833 1694757784764271552623625)
            ·
              refine ⟨1271068338573203664467719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694757784764271552623625 1271068338573203664467719)
              ·
                refine ⟨1906602507859805496701579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271068338573203664467719 1906602507859805496701579)
                ·
                  refine ⟨2859903761789708245052369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906602507859805496701579 2859903761789708245052369)
                  ·
                    refine ⟨2144927821342281183789277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859903761789708245052369 2144927821342281183789277)
                    ·
                      refine ⟨804347933003355443920979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2144927821342281183789277 804347933003355443920979)
                      ·
                        rfl

theorem cell23_1566462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1566462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566462 prefixEnd_1566462 := by exact prefixLift 1566462
  have htrace : WordTrace (prefixWord ++ tailWord_1566462) baseStart_1566462 baseEnd_1566462 := by
    simpa [prefixWord, tailWord_1566462, baseEnd_1566462] using wordTrace_append hprefix tailTrace_1566462
  have hstable : (prefixWord ++ tailWord_1566462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566462).length < 2 ^ (prefixWord ++ tailWord_1566462).sum := by decide
  have hdescent : baseEnd_1566462 < baseStart_1566462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566474 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1566474 : Nat := 118140960795 + 1566474 * 2 ^ 59
def prefixEnd_1566474 : Nat := 4983230072969 + 3 ^ 40 * 1566474 * 2
def baseEnd_1566474 : Nat := 268118031590403132323641

theorem tailTrace_1566474 : CollatzResearch.WordTrace tailWord_1566474 prefixEnd_1566474 268118031590403132323641 := by
  unfold tailWord_1566474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283500131734926326240619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38089333684626470203308317 14283500131734926326240619)
  ·
    refine ⟨21425250197602389489360929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14283500131734926326240619 21425250197602389489360929)
    ·
      refine ⟨16068937648201792117020697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21425250197602389489360929 16068937648201792117020697)
      ·
        refine ⟨12051703236151344087765523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16068937648201792117020697 12051703236151344087765523)
        ·
          refine ⟨18077554854227016131648285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12051703236151344087765523 18077554854227016131648285)
          ·
            refine ⟨6779083070335131049368107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18077554854227016131648285 6779083070335131049368107)
            ·
              refine ⟨10168624605502696574052161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779083070335131049368107 10168624605502696574052161)
              ·
                refine ⟨7626468454127022430539121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10168624605502696574052161 7626468454127022430539121)
                ·
                  refine ⟨5719851340595266822904341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7626468454127022430539121 5719851340595266822904341)
                  ·
                    refine ⟨268118031590403132323641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5719851340595266822904341 268118031590403132323641)
                    ·
                      rfl

theorem cell23_1566474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1566474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566474 prefixEnd_1566474 := by exact prefixLift 1566474
  have htrace : WordTrace (prefixWord ++ tailWord_1566474) baseStart_1566474 baseEnd_1566474 := by
    simpa [prefixWord, tailWord_1566474, baseEnd_1566474] using wordTrace_append hprefix tailTrace_1566474
  have hstable : (prefixWord ++ tailWord_1566474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566474).length < 2 ^ (prefixWord ++ tailWord_1566474).sum := by decide
  have hdescent : baseEnd_1566474 < baseStart_1566474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566518 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1566518 : Nat := 118140960795 + 1566518 * 2 ^ 59
def prefixEnd_1566518 : Nat := 4983230072969 + 3 ^ 40 * 1566518 * 2
def baseEnd_1566518 : Nat := 804376687920007224820721

theorem tailTrace_1566518 : CollatzResearch.WordTrace tailWord_1566518 prefixEnd_1566518 804376687920007224820721 := by
  unfold tailWord_1566518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570975333673768801222763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38090403559186867213042805 3570975333673768801222763)
  ·
    refine ⟨5356463000510653201834145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3570975333673768801222763 5356463000510653201834145)
    ·
      refine ⟨4017347250382989901375609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5356463000510653201834145 4017347250382989901375609)
      ·
        refine ⟨3013010437787242426031707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017347250382989901375609 3013010437787242426031707)
        ·
          refine ⟨4519515656680863639047561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013010437787242426031707 4519515656680863639047561)
          ·
            refine ⟨3389636742510647729285671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4519515656680863639047561 3389636742510647729285671)
            ·
              refine ⟨5084455113765971593928507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389636742510647729285671 5084455113765971593928507)
              ·
                refine ⟨7626682670648957390892761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084455113765971593928507 7626682670648957390892761)
                ·
                  refine ⟨5720012002986718043169571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7626682670648957390892761 5720012002986718043169571)
                  ·
                    refine ⟨8580018004480077064754357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5720012002986718043169571 8580018004480077064754357)
                    ·
                      refine ⟨804376687920007224820721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8580018004480077064754357 804376687920007224820721)
                      ·
                        rfl

theorem cell23_1566518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1566518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566518 prefixEnd_1566518 := by exact prefixLift 1566518
  have htrace : WordTrace (prefixWord ++ tailWord_1566518) baseStart_1566518 baseEnd_1566518 := by
    simpa [prefixWord, tailWord_1566518, baseEnd_1566518] using wordTrace_append hprefix tailTrace_1566518
  have hstable : (prefixWord ++ tailWord_1566518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566518).length < 2 ^ (prefixWord ++ tailWord_1566518).sum := by decide
  have hdescent : baseEnd_1566518 < baseStart_1566518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566538 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_1566538 : Nat := 118140960795 + 1566538 * 2 ^ 59
def prefixEnd_1566538 : Nat := 4983230072969 + 3 ^ 40 * 1566538 * 2
def baseEnd_1566538 : Nat := 89376328614788571841181

theorem tailTrace_1566538 : CollatzResearch.WordTrace tailWord_1566538 prefixEnd_1566538 89376328614788571841181 := by
  unfold tailWord_1566538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284083699676961058823067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38090889865805229490194845 14284083699676961058823067)
  ·
    refine ⟨21426125549515441588234601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14284083699676961058823067 21426125549515441588234601)
    ·
      refine ⟨16069594162136581191175951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21426125549515441588234601 16069594162136581191175951)
      ·
        refine ⟨24104391243204871786763927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16069594162136581191175951 24104391243204871786763927)
        ·
          refine ⟨36156586864807307680145891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24104391243204871786763927 36156586864807307680145891)
          ·
            refine ⟨54234880297210961520218837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36156586864807307680145891 54234880297210961520218837)
            ·
              refine ⟨1271130006965881910630129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54234880297210961520218837 1271130006965881910630129)
              ·
                refine ⟨953347505224411432972597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271130006965881910630129 953347505224411432972597)
                ·
                  refine ⟨89376328614788571841181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 953347505224411432972597 89376328614788571841181)
                  ·
                    rfl

theorem cell23_1566538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_1566538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566538 prefixEnd_1566538 := by exact prefixLift 1566538
  have htrace : WordTrace (prefixWord ++ tailWord_1566538) baseStart_1566538 baseEnd_1566538 := by
    simpa [prefixWord, tailWord_1566538, baseEnd_1566538] using wordTrace_append hprefix tailTrace_1566538
  have hstable : (prefixWord ++ tailWord_1566538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566538).length < 2 ^ (prefixWord ++ tailWord_1566538).sum := by decide
  have hdescent : baseEnd_1566538 < baseStart_1566538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566571 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 4, 4, 2]
def baseStart_1566571 : Nat := 118140960795 + 1566571 * 2 ^ 59
def prefixEnd_1566571 : Nat := 4983230072969 + 3 ^ 40 * 1566571 * 2
def baseEnd_1566571 : Nat := 804403902394695517457977

theorem tailTrace_1566571 : CollatzResearch.WordTrace tailWord_1566571 prefixEnd_1566571 804403902394695517457977 := by
  unfold tailWord_1566571
  simp only [CollatzResearch.WordTrace]
  refine ⟨57137538407588290871243567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38091692271725527247495711 57137538407588290871243567)
  ·
    refine ⟨85706307611382436306865351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57137538407588290871243567 85706307611382436306865351)
    ·
      refine ⟨128559461417073654460298027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85706307611382436306865351 128559461417073654460298027)
      ·
        refine ⟨192839192125610481690447041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128559461417073654460298027 192839192125610481690447041)
        ·
          refine ⟨144629394094207861267835281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192839192125610481690447041 144629394094207861267835281)
          ·
            refine ⟨108472045570655895950876461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144629394094207861267835281 108472045570655895950876461)
            ·
              refine ⟨40677017088995960981578673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108472045570655895950876461 40677017088995960981578673)
              ·
                refine ⟨30507762816746970736184005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40677017088995960981578673 30507762816746970736184005)
                ·
                  refine ⟨5720205528140057013034501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30507762816746970736184005 5720205528140057013034501)
                  ·
                    refine ⟨1072538536526260689943969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720205528140057013034501 1072538536526260689943969)
                    ·
                      refine ⟨804403902394695517457977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072538536526260689943969 804403902394695517457977)
                      ·
                        rfl

theorem cell23_1566571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4, 2].length) (baseStart_1566571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566571 prefixEnd_1566571 := by exact prefixLift 1566571
  have htrace : WordTrace (prefixWord ++ tailWord_1566571) baseStart_1566571 baseEnd_1566571 := by
    simpa [prefixWord, tailWord_1566571, baseEnd_1566571] using wordTrace_append hprefix tailTrace_1566571
  have hstable : (prefixWord ++ tailWord_1566571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566571).length < 2 ^ (prefixWord ++ tailWord_1566571).sum := by decide
  have hdescent : baseEnd_1566571 < baseStart_1566571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566584 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1566584 : Nat := 118140960795 + 1566584 * 2 ^ 59
def prefixEnd_1566584 : Nat := 4983230072969 + 3 ^ 40 * 1566584 * 2
def baseEnd_1566584 : Nat := 804410577643203966595417

theorem tailTrace_1566584 : CollatzResearch.WordTrace tailWord_1566584 prefixEnd_1566584 804410577643203966595417 := by
  unfold tailWord_1566584
  simp only [CollatzResearch.WordTrace]
  refine ⟨28569006278270597045733403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38092008371027462727644537 28569006278270597045733403)
  ·
    refine ⟨42853509417405895568600105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28569006278270597045733403 42853509417405895568600105)
    ·
      refine ⟨32140132063054421676450079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42853509417405895568600105 32140132063054421676450079)
      ·
        refine ⟨48210198094581632514675119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32140132063054421676450079 48210198094581632514675119)
        ·
          refine ⟨72315297141872448772012679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48210198094581632514675119 72315297141872448772012679)
          ·
            refine ⟨108472945712808673158019019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72315297141872448772012679 108472945712808673158019019)
            ·
              refine ⟨162709418569213009737028529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108472945712808673158019019 162709418569213009737028529)
              ·
                refine ⟨122032063926909757302771397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162709418569213009737028529 122032063926909757302771397)
                ·
                  refine ⟨22881011986295579494269637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122032063926909757302771397 22881011986295579494269637)
                  ·
                    refine ⟨4290189747430421155175557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22881011986295579494269637 4290189747430421155175557)
                    ·
                      refine ⟨804410577643203966595417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4290189747430421155175557 804410577643203966595417)
                      ·
                        rfl

theorem cell23_1566584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1566584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566584 prefixEnd_1566584 := by exact prefixLift 1566584
  have htrace : WordTrace (prefixWord ++ tailWord_1566584) baseStart_1566584 baseEnd_1566584 := by
    simpa [prefixWord, tailWord_1566584, baseEnd_1566584] using wordTrace_append hprefix tailTrace_1566584
  have hstable : (prefixWord ++ tailWord_1566584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566584).length < 2 ^ (prefixWord ++ tailWord_1566584).sum := by decide
  have hdescent : baseEnd_1566584 < baseStart_1566584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566648 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 4, 3, 2]
def baseStart_1566648 : Nat := 118140960795 + 1566648 * 2 ^ 59
def prefixEnd_1566648 : Nat := 4983230072969 + 3 ^ 40 * 1566648 * 2
def baseEnd_1566648 : Nat := 804443440405091716195123

theorem tailTrace_1566648 : CollatzResearch.WordTrace tailWord_1566648 prefixEnd_1566648 804443440405091716195123 := by
  unfold tailWord_1566648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28570173414154666510898299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38093564552206222014531065 28570173414154666510898299)
  ·
    refine ⟨42855260121231999766347449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28570173414154666510898299 42855260121231999766347449)
    ·
      refine ⟨32141445090923999824760587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42855260121231999766347449 32141445090923999824760587)
      ·
        refine ⟨48212167636385999737140881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32141445090923999824760587 48212167636385999737140881)
        ·
          refine ⟨36159125727289499802855661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48212167636385999737140881 36159125727289499802855661)
          ·
            refine ⟨13559672147733562426070873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36159125727289499802855661 13559672147733562426070873)
            ·
              refine ⟨10169754110800171819553155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13559672147733562426070873 10169754110800171819553155)
              ·
                refine ⟨15254631166200257729329733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169754110800171819553155 15254631166200257729329733)
                ·
                  refine ⟨2860243343662548324249325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15254631166200257729329733 2860243343662548324249325)
                  ·
                    refine ⟨1072591253873455621593497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860243343662548324249325 1072591253873455621593497)
                    ·
                      refine ⟨804443440405091716195123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072591253873455621593497 804443440405091716195123)
                      ·
                        rfl

theorem cell23_1566648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_1566648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566648 prefixEnd_1566648 := by exact prefixLift 1566648
  have htrace : WordTrace (prefixWord ++ tailWord_1566648) baseStart_1566648 baseEnd_1566648 := by
    simpa [prefixWord, tailWord_1566648, baseEnd_1566648] using wordTrace_append hprefix tailTrace_1566648
  have hstable : (prefixWord ++ tailWord_1566648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566648).length < 2 ^ (prefixWord ++ tailWord_1566648).sum := by decide
  have hdescent : baseEnd_1566648 < baseStart_1566648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566655 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 1, 1, 3]
def baseStart_1566655 : Nat := 118140960795 + 1566655 * 2 ^ 59
def prefixEnd_1566655 : Nat := 4983230072969 + 3 ^ 40 * 1566655 * 2
def baseEnd_1566655 : Nat := 804447034769673188807591

theorem tailTrace_1566655 : CollatzResearch.WordTrace tailWord_1566655 prefixEnd_1566655 804447034769673188807591 := by
  unfold tailWord_1566655
  simp only [CollatzResearch.WordTrace]
  refine ⟨57140602139283973217301419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38093734759522648811534279 57140602139283973217301419)
  ·
    refine ⟨85710903208925959825952129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57140602139283973217301419 85710903208925959825952129)
    ·
      refine ⟨64283177406694469869464097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85710903208925959825952129 64283177406694469869464097)
      ·
        refine ⟨48212383055020852402098073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64283177406694469869464097 48212383055020852402098073)
        ·
          refine ⟨36159287291265639301573555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48212383055020852402098073 36159287291265639301573555)
          ·
            refine ⟨54238930936898458952360333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36159287291265639301573555 54238930936898458952360333)
            ·
              refine ⟨20339599101336922107135125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54238930936898458952360333 20339599101336922107135125)
              ·
                refine ⟨953418707875168223771959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20339599101336922107135125 953418707875168223771959)
                ·
                  refine ⟨1430128061812752335657939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953418707875168223771959 1430128061812752335657939)
                  ·
                    refine ⟨2145192092719128503486909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1430128061812752335657939 2145192092719128503486909)
                    ·
                      refine ⟨804447034769673188807591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2145192092719128503486909 804447034769673188807591)
                      ·
                        rfl

theorem cell23_1566655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_1566655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566655 prefixEnd_1566655 := by exact prefixLift 1566655
  have htrace : WordTrace (prefixWord ++ tailWord_1566655) baseStart_1566655 baseEnd_1566655 := by
    simpa [prefixWord, tailWord_1566655, baseEnd_1566655] using wordTrace_append hprefix tailTrace_1566655
  have hstable : (prefixWord ++ tailWord_1566655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566655).length < 2 ^ (prefixWord ++ tailWord_1566655).sum := by decide
  have hdescent : baseEnd_1566655 < baseStart_1566655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566661 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_1566661 : Nat := 118140960795 + 1566661 * 2 ^ 59
def prefixEnd_1566661 : Nat := 4983230072969 + 3 ^ 40 * 1566661 * 2
def baseEnd_1566661 : Nat := 804450115653600165332563

theorem tailTrace_1566661 : CollatzResearch.WordTrace tailWord_1566661 prefixEnd_1566661 804450115653600165332563 := by
  unfold tailWord_1566661
  simp only [CollatzResearch.WordTrace]
  refine ⟨57140820977262236242019837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38093880651508157494679891 57140820977262236242019837)
  ·
    refine ⟨21427807866473338590757439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57140820977262236242019837 21427807866473338590757439)
    ·
      refine ⟨32141711799710007886136159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21427807866473338590757439 32141711799710007886136159)
      ·
        refine ⟨48212567699565011829204239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32141711799710007886136159 48212567699565011829204239)
        ·
          refine ⟨72318851549347517743806359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48212567699565011829204239 72318851549347517743806359)
          ·
            refine ⟨108478277324021276615709539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72318851549347517743806359 108478277324021276615709539)
            ·
              refine ⟨162717415986031914923564309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108478277324021276615709539 162717415986031914923564309)
              ·
                refine ⟨7627378874345246012042077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162717415986031914923564309 7627378874345246012042077)
                ·
                  refine ⟨2860267077879467254515779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7627378874345246012042077 2860267077879467254515779)
                  ·
                    refine ⟨4290400616819200881773669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2860267077879467254515779 4290400616819200881773669)
                    ·
                      refine ⟨804450115653600165332563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4290400616819200881773669 804450115653600165332563)
                      ·
                        rfl

theorem cell23_1566661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_1566661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566661 prefixEnd_1566661 := by exact prefixLift 1566661
  have htrace : WordTrace (prefixWord ++ tailWord_1566661) baseStart_1566661 baseEnd_1566661 := by
    simpa [prefixWord, tailWord_1566661, baseEnd_1566661] using wordTrace_append hprefix tailTrace_1566661
  have hstable : (prefixWord ++ tailWord_1566661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566661).length < 2 ^ (prefixWord ++ tailWord_1566661).sum := by decide
  have hdescent : baseEnd_1566661 < baseStart_1566661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566698 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1566698 : Nat := 118140960795 + 1566698 * 2 ^ 59
def prefixEnd_1566698 : Nat := 4983230072969 + 3 ^ 40 * 1566698 * 2
def baseEnd_1566698 : Nat := 804469114437816520569893

theorem tailTrace_1566698 : CollatzResearch.WordTrace tailWord_1566698 prefixEnd_1566698 804469114437816520569893 := by
  unfold tailWord_1566698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14285542619532047890279187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38094780318752127707411165 14285542619532047890279187)
  ·
    refine ⟨21428313929298071835418781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14285542619532047890279187 21428313929298071835418781)
    ·
      refine ⟨8035617723486776938282043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21428313929298071835418781 8035617723486776938282043)
      ·
        refine ⟨12053426585230165407423065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035617723486776938282043 12053426585230165407423065)
        ·
          refine ⟨9040069938922624055567299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12053426585230165407423065 9040069938922624055567299)
          ·
            refine ⟨13560104908383936083350949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040069938922624055567299 13560104908383936083350949)
            ·
              refine ⟨2542519670321988015628303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13560104908383936083350949 2542519670321988015628303)
              ·
                refine ⟨3813779505482982023442455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542519670321988015628303 3813779505482982023442455)
                ·
                  refine ⟨5720669258224473035163683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813779505482982023442455 5720669258224473035163683)
                  ·
                    refine ⟨8581003887336709552745525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5720669258224473035163683 8581003887336709552745525)
                    ·
                      refine ⟨804469114437816520569893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8581003887336709552745525 804469114437816520569893)
                      ·
                        rfl

theorem cell23_1566698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1566698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566698 prefixEnd_1566698 := by exact prefixLift 1566698
  have htrace : WordTrace (prefixWord ++ tailWord_1566698) baseStart_1566698 baseEnd_1566698 := by
    simpa [prefixWord, tailWord_1566698, baseEnd_1566698] using wordTrace_append hprefix tailTrace_1566698
  have hstable : (prefixWord ++ tailWord_1566698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566698).length < 2 ^ (prefixWord ++ tailWord_1566698).sum := by decide
  have hdescent : baseEnd_1566698 < baseStart_1566698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566712 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 1, 2, 2]
def baseStart_1566712 : Nat := 118140960795 + 1566712 * 2 ^ 59
def prefixEnd_1566712 : Nat := 4983230072969 + 3 ^ 40 * 1566712 * 2
def baseEnd_1566712 : Nat := 804476303166979465794829

theorem tailTrace_1566712 : CollatzResearch.WordTrace tailWord_1566712 prefixEnd_1566712 804476303166979465794829 := by
  unfold tailWord_1566712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571340550038735976063195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38095120733384981301417593 28571340550038735976063195)
  ·
    refine ⟨42857010825058103964094793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28571340550038735976063195 42857010825058103964094793)
    ·
      refine ⟨32142758118793577973071095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42857010825058103964094793 32142758118793577973071095)
      ·
        refine ⟨48214137178190366959606643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32142758118793577973071095 48214137178190366959606643)
        ·
          refine ⟨72321205767285550439409965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48214137178190366959606643 72321205767285550439409965)
          ·
            refine ⟨27120452162732081414778737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72321205767285550439409965 27120452162732081414778737)
            ·
              refine ⟨20340339122049061061084053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27120452162732081414778737 20340339122049061061084053)
              ·
                refine ⟨953453396346049737238315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20340339122049061061084053 953453396346049737238315)
                ·
                  refine ⟨1430180094519074605857473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953453396346049737238315 1430180094519074605857473)
                  ·
                    refine ⟨1072635070889305954393105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1430180094519074605857473 1072635070889305954393105)
                    ·
                      refine ⟨804476303166979465794829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072635070889305954393105 804476303166979465794829)
                      ·
                        rfl

theorem cell23_1566712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_1566712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566712 prefixEnd_1566712 := by exact prefixLift 1566712
  have htrace : WordTrace (prefixWord ++ tailWord_1566712) baseStart_1566712 baseEnd_1566712 := by
    simpa [prefixWord, tailWord_1566712, baseEnd_1566712] using wordTrace_append hprefix tailTrace_1566712
  have hstable : (prefixWord ++ tailWord_1566712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566712).length < 2 ^ (prefixWord ++ tailWord_1566712).sum := by decide
  have hdescent : baseEnd_1566712 < baseStart_1566712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566718 : List Nat := [4, 2, 2, 2, 1, 1, 1, 10]
def baseStart_1566718 : Nat := 118140960795 + 1566718 * 2 ^ 59
def prefixEnd_1566718 : Nat := 4983230072969 + 3 ^ 40 * 1566718 * 2
def baseEnd_1566718 : Nat := 29795532742626164530363

theorem tailTrace_1566718 : CollatzResearch.WordTrace tailWord_1566718 prefixEnd_1566718 29795532742626164530363 := by
  unfold tailWord_1566718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142862492256966872105601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38095266625370489984563205 7142862492256966872105601)
  ·
    refine ⟨5357146869192725154079201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7142862492256966872105601 5357146869192725154079201)
    ·
      refine ⟨4017860151894543865559401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5357146869192725154079201 4017860151894543865559401)
      ·
        refine ⟨3013395113920907899169551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017860151894543865559401 3013395113920907899169551)
        ·
          refine ⟨4520092670881361848754327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013395113920907899169551 4520092670881361848754327)
          ·
            refine ⟨6780139006322042773131491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520092670881361848754327 6780139006322042773131491)
            ·
              refine ⟨10170208509483064159697237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6780139006322042773131491 10170208509483064159697237)
              ·
                refine ⟨29795532742626164530363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10170208509483064159697237 29795532742626164530363)
                ·
                  rfl

theorem cell23_1566718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_1566718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566718 prefixEnd_1566718 := by exact prefixLift 1566718
  have htrace : WordTrace (prefixWord ++ tailWord_1566718) baseStart_1566718 baseEnd_1566718 := by
    simpa [prefixWord, tailWord_1566718, baseEnd_1566718] using wordTrace_append hprefix tailTrace_1566718
  have hstable : (prefixWord ++ tailWord_1566718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566718).length < 2 ^ (prefixWord ++ tailWord_1566718).sum := by decide
  have hdescent : baseEnd_1566718 < baseStart_1566718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566721 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1566721 : Nat := 118140960795 + 1566721 * 2 ^ 59
def prefixEnd_1566721 : Nat := 4983230072969 + 3 ^ 40 * 1566721 * 2
def baseEnd_1566721 : Nat := 804480924492869930582287

theorem tailTrace_1566721 : CollatzResearch.WordTrace tailWord_1566721 prefixEnd_1566721 804480924492869930582287 := by
  unfold tailWord_1566721
  simp only [CollatzResearch.WordTrace]
  refine ⟨57143009357044866489204017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38095339571363244326136011 57143009357044866489204017)
  ·
    refine ⟨42857257017783649866903013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57143009357044866489204017 42857257017783649866903013)
    ·
      refine ⟨8035735690834434350044315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42857257017783649866903013 8035735690834434350044315)
      ·
        refine ⟨12053603536251651525066473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035735690834434350044315 12053603536251651525066473)
        ·
          refine ⟨9040202652188738643799855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12053603536251651525066473 9040202652188738643799855)
          ·
            refine ⟨13560303978283107965699783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040202652188738643799855 13560303978283107965699783)
            ·
              refine ⟨20340455967424661948549675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13560303978283107965699783 20340455967424661948549675)
              ·
                refine ⟨30510683951136992922824513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20340455967424661948549675 30510683951136992922824513)
                ·
                  refine ⟨22883012963352744692118385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30510683951136992922824513 22883012963352744692118385)
                  ·
                    refine ⟨17162259722514558519088789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22883012963352744692118385 17162259722514558519088789)
                    ·
                      refine ⟨804480924492869930582287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17162259722514558519088789 804480924492869930582287)
                      ·
                        rfl

theorem cell23_1566721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1566721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566721 prefixEnd_1566721 := by exact prefixLift 1566721
  have htrace : WordTrace (prefixWord ++ tailWord_1566721) baseStart_1566721 baseEnd_1566721 := by
    simpa [prefixWord, tailWord_1566721, baseEnd_1566721] using wordTrace_append hprefix tailTrace_1566721
  have hstable : (prefixWord ++ tailWord_1566721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566721).length < 2 ^ (prefixWord ++ tailWord_1566721).sum := by decide
  have hdescent : baseEnd_1566721 < baseStart_1566721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566728 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1566728 : Nat := 118140960795 + 1566728 * 2 ^ 59
def prefixEnd_1566728 : Nat := 4983230072969 + 3 ^ 40 * 1566728 * 2
def baseEnd_1566728 : Nat := 804484518857451403194755

theorem tailTrace_1566728 : CollatzResearch.WordTrace tailWord_1566728 prefixEnd_1566728 804484518857451403194755 := by
  unfold tailWord_1566728
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571632334009753342354419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38095509778679671123139225 28571632334009753342354419)
  ·
    refine ⟨42857448501014630013531629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28571632334009753342354419 42857448501014630013531629)
    ·
      refine ⟨16071543187880486255074361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42857448501014630013531629 16071543187880486255074361)
      ·
        refine ⟨12053657390910364691305771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16071543187880486255074361 12053657390910364691305771)
        ·
          refine ⟨18080486086365547036958657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053657390910364691305771 18080486086365547036958657)
          ·
            refine ⟨13560364564774160277718993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18080486086365547036958657 13560364564774160277718993)
            ·
              refine ⟨10170273423580620208289245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13560364564774160277718993 10170273423580620208289245)
              ·
                refine ⟨3813852533842732578108467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10170273423580620208289245 3813852533842732578108467)
                ·
                  refine ⟨5720778800764098867162701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813852533842732578108467 5720778800764098867162701)
                  ·
                    refine ⟨2145292050286537075186013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5720778800764098867162701 2145292050286537075186013)
                    ·
                      refine ⟨804484518857451403194755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2145292050286537075186013 804484518857451403194755)
                      ·
                        rfl

theorem cell23_1566728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1566728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566728 prefixEnd_1566728 := by exact prefixLift 1566728
  have htrace : WordTrace (prefixWord ++ tailWord_1566728) baseStart_1566728 baseEnd_1566728 := by
    simpa [prefixWord, tailWord_1566728, baseEnd_1566728] using wordTrace_append hprefix tailTrace_1566728
  have hstable : (prefixWord ++ tailWord_1566728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566728).length < 2 ^ (prefixWord ++ tailWord_1566728).sum := by decide
  have hdescent : baseEnd_1566728 < baseStart_1566728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566762 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1566762 : Nat := 118140960795 + 1566762 * 2 ^ 59
def prefixEnd_1566762 : Nat := 4983230072969 + 3 ^ 40 * 1566762 * 2
def baseEnd_1566762 : Nat := 804501977199704270169599

theorem tailTrace_1566762 : CollatzResearch.WordTrace tailWord_1566762 prefixEnd_1566762 804501977199704270169599 := by
  unfold tailWord_1566762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286126187474082622861635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38096336499930886994297693 14286126187474082622861635)
  ·
    refine ⟨21429189281211123934292453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14286126187474082622861635 21429189281211123934292453)
    ·
      refine ⟨4017972990227085737679835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21429189281211123934292453 4017972990227085737679835)
      ·
        refine ⟨6026959485340628606519753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017972990227085737679835 6026959485340628606519753)
        ·
          refine ⟨4520219614005471454889815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6026959485340628606519753 4520219614005471454889815)
          ·
            refine ⟨6780329421008207182334723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520219614005471454889815 6780329421008207182334723)
            ·
              refine ⟨10170494131512310773502085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6780329421008207182334723 10170494131512310773502085)
              ·
                refine ⟨1906967649658558270031641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10170494131512310773502085 1906967649658558270031641)
                ·
                  refine ⟨1430225737243918702523731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1906967649658558270031641 1430225737243918702523731)
                  ·
                    refine ⟨2145338605865878053785597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1430225737243918702523731 2145338605865878053785597)
                    ·
                      refine ⟨804501977199704270169599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2145338605865878053785597 804501977199704270169599)
                      ·
                        rfl

theorem cell23_1566762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1566762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566762 prefixEnd_1566762 := by exact prefixLift 1566762
  have htrace : WordTrace (prefixWord ++ tailWord_1566762) baseStart_1566762 baseEnd_1566762 := by
    simpa [prefixWord, tailWord_1566762, baseEnd_1566762] using wordTrace_append hprefix tailTrace_1566762
  have hstable : (prefixWord ++ tailWord_1566762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566762).length < 2 ^ (prefixWord ++ tailWord_1566762).sum := by decide
  have hdescent : baseEnd_1566762 < baseStart_1566762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566771 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_1566771 : Nat := 118140960795 + 1566771 * 2 ^ 59
def prefixEnd_1566771 : Nat := 4983230072969 + 3 ^ 40 * 1566771 * 2
def baseEnd_1566771 : Nat := 804506598525594734957057

theorem tailTrace_1566771 : CollatzResearch.WordTrace tailWord_1566771 prefixEnd_1566771 804506598525594734957057 := by
  unfold tailWord_1566771
  simp only [CollatzResearch.WordTrace]
  refine ⟨57144833006863725028524167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38096555337909150019016111 57144833006863725028524167)
  ·
    refine ⟨85717249510295587542786251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57144833006863725028524167 85717249510295587542786251)
    ·
      refine ⟨128575874265443381314179377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85717249510295587542786251 128575874265443381314179377)
      ·
        refine ⟨96431905699082535985634533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128575874265443381314179377 96431905699082535985634533)
        ·
          refine ⟨18080982318577975497306475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96431905699082535985634533 18080982318577975497306475)
          ·
            refine ⟨27121473477866963245959713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18080982318577975497306475 27121473477866963245959713)
            ·
              refine ⟨20341105108400222434469785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27121473477866963245959713 20341105108400222434469785)
              ·
                refine ⟨15255828831300166825852339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20341105108400222434469785 15255828831300166825852339)
                ·
                  refine ⟨22883743246950250238778509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15255828831300166825852339 22883743246950250238778509)
                  ·
                    refine ⟨8581403717606343839541941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22883743246950250238778509 8581403717606343839541941)
                    ·
                      refine ⟨804506598525594734957057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8581403717606343839541941 804506598525594734957057)
                      ·
                        rfl

theorem cell23_1566771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_1566771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566771 prefixEnd_1566771 := by exact prefixLift 1566771
  have htrace : WordTrace (prefixWord ++ tailWord_1566771) baseStart_1566771 baseEnd_1566771 := by
    simpa [prefixWord, tailWord_1566771, baseEnd_1566771] using wordTrace_append hprefix tailTrace_1566771
  have hstable : (prefixWord ++ tailWord_1566771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566771).length < 2 ^ (prefixWord ++ tailWord_1566771).sum := by decide
  have hdescent : baseEnd_1566771 < baseStart_1566771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566801 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1566801 : Nat := 118140960795 + 1566801 * 2 ^ 59
def prefixEnd_1566801 : Nat := 4983230072969 + 3 ^ 40 * 1566801 * 2
def baseEnd_1566801 : Nat := 804522002945229617581919

theorem tailTrace_1566801 : CollatzResearch.WordTrace tailWord_1566801 prefixEnd_1566801 804522002945229617581919 := by
  unfold tailWord_1566801
  simp only [CollatzResearch.WordTrace]
  refine ⟨57145927196755040152116257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38097284797836693434744171 57145927196755040152116257)
  ·
    refine ⟨42859445397566280114087193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57145927196755040152116257 42859445397566280114087193)
    ·
      refine ⟨32144584048174710085565395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42859445397566280114087193 32144584048174710085565395)
      ·
        refine ⟨48216876072262065128348093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32144584048174710085565395 48216876072262065128348093)
        ·
          refine ⟨18081328527098274423130535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48216876072262065128348093 18081328527098274423130535)
          ·
            refine ⟨27121992790647411634695803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18081328527098274423130535 27121992790647411634695803)
            ·
              refine ⟨40682989185971117452043705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27121992790647411634695803 40682989185971117452043705)
              ·
                refine ⟨30512241889478338089032779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40682989185971117452043705 30512241889478338089032779)
                ·
                  refine ⟨45768362834217507133549169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30512241889478338089032779 45768362834217507133549169)
                  ·
                    refine ⟨34326272125663130350161877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45768362834217507133549169 34326272125663130350161877)
                    ·
                      refine ⟨804522002945229617581919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34326272125663130350161877 804522002945229617581919)
                      ·
                        rfl

theorem cell23_1566801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1566801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566801 prefixEnd_1566801 := by exact prefixLift 1566801
  have htrace : WordTrace (prefixWord ++ tailWord_1566801) baseStart_1566801 baseEnd_1566801 := by
    simpa [prefixWord, tailWord_1566801, baseEnd_1566801] using wordTrace_append hprefix tailTrace_1566801
  have hstable : (prefixWord ++ tailWord_1566801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566801).length < 2 ^ (prefixWord ++ tailWord_1566801).sum := by decide
  have hdescent : baseEnd_1566801 < baseStart_1566801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566806 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1566806 : Nat := 118140960795 + 1566806 * 2 ^ 59
def prefixEnd_1566806 : Nat := 4983230072969 + 3 ^ 40 * 1566806 * 2
def baseEnd_1566806 : Nat := 804524570348502098019397

theorem tailTrace_1566806 : CollatzResearch.WordTrace tailWord_1566806 prefixEnd_1566806 804524570348502098019397 := by
  unfold tailWord_1566806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571631847608557875378017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38097406374491284004032181 3571631847608557875378017)
  ·
    refine ⟨2678723885706418406533513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3571631847608557875378017 2678723885706418406533513)
    ·
      refine ⟨2009042914279813804900135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2678723885706418406533513 2009042914279813804900135)
      ·
        refine ⟨3013564371419720707350203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009042914279813804900135 3013564371419720707350203)
        ·
          refine ⟨4520346557129581061025305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013564371419720707350203 4520346557129581061025305)
          ·
            refine ⟨3390259917847185795768979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520346557129581061025305 3390259917847185795768979)
            ·
              refine ⟨5085389876770778693653469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390259917847185795768979 5085389876770778693653469)
              ·
                refine ⟨1907021203789042010120051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5085389876770778693653469 1907021203789042010120051)
                ·
                  refine ⟨2860531805683563015180077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907021203789042010120051 2860531805683563015180077)
                  ·
                    refine ⟨1072699427131336130692529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2860531805683563015180077 1072699427131336130692529)
                    ·
                      refine ⟨804524570348502098019397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072699427131336130692529 804524570348502098019397)
                      ·
                        rfl

theorem cell23_1566806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1566806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566806 prefixEnd_1566806 := by exact prefixLift 1566806
  have htrace : WordTrace (prefixWord ++ tailWord_1566806) baseStart_1566806 baseEnd_1566806 := by
    simpa [prefixWord, tailWord_1566806, baseEnd_1566806] using wordTrace_append hprefix tailTrace_1566806
  have hstable : (prefixWord ++ tailWord_1566806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566806).length < 2 ^ (prefixWord ++ tailWord_1566806).sum := by decide
  have hdescent : baseEnd_1566806 < baseStart_1566806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566912 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_1566912 : Nat := 118140960795 + 1566912 * 2 ^ 59
def prefixEnd_1566912 : Nat := 4983230072969 + 3 ^ 40 * 1566912 * 2
def baseEnd_1566912 : Nat := 804578999297878683293909

theorem tailTrace_1566912 : CollatzResearch.WordTrace tailWord_1566912 prefixEnd_1566912 804578999297878683293909 := by
  unfold tailWord_1566912
  simp only [CollatzResearch.WordTrace]
  refine ⟨28574987849676453054703495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38099983799568604072937993 28574987849676453054703495)
  ·
    refine ⟨42862481774514679582055243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28574987849676453054703495 42862481774514679582055243)
    ·
      refine ⟨64293722661772019373082865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42862481774514679582055243 64293722661772019373082865)
      ·
        refine ⟨48220291996329014529812149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64293722661772019373082865 48220291996329014529812149)
        ·
          refine ⟨4520652374655845112169889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48220291996329014529812149 4520652374655845112169889)
          ·
            refine ⟨3390489280991883834127417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520652374655845112169889 3390489280991883834127417)
            ·
              refine ⟨2542866960743912875595563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390489280991883834127417 2542866960743912875595563)
              ·
                refine ⟨3814300441115869313393345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542866960743912875595563 3814300441115869313393345)
                ·
                  refine ⟨2860725330836901985045009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814300441115869313393345 2860725330836901985045009)
                  ·
                    refine ⟨2145543998127676488783757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2860725330836901985045009 2145543998127676488783757)
                    ·
                      refine ⟨804578999297878683293909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2145543998127676488783757 804578999297878683293909)
                      ·
                        rfl

theorem cell23_1566912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_1566912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566912 prefixEnd_1566912 := by exact prefixLift 1566912
  have htrace : WordTrace (prefixWord ++ tailWord_1566912) baseStart_1566912 baseEnd_1566912 := by
    simpa [prefixWord, tailWord_1566912, baseEnd_1566912] using wordTrace_append hprefix tailTrace_1566912
  have hstable : (prefixWord ++ tailWord_1566912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566912).length < 2 ^ (prefixWord ++ tailWord_1566912).sum := by decide
  have hdescent : baseEnd_1566912 < baseStart_1566912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566935 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 3, 5, 2]
def baseStart_1566935 : Nat := 118140960795 + 1566935 * 2 ^ 59
def prefixEnd_1566935 : Nat := 4983230072969 + 3 ^ 40 * 1566935 * 2
def baseEnd_1566935 : Nat := 804590809352932093306303

theorem tailTrace_1566935 : CollatzResearch.WordTrace tailWord_1566935 prefixEnd_1566935 804590809352932093306303 := by
  unfold tailWord_1566935
  simp only [CollatzResearch.WordTrace]
  refine ⟨57150814578269581037494259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38100543052179720691662839 57150814578269581037494259)
  ·
    refine ⟨85726221867404371556241389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57150814578269581037494259 85726221867404371556241389)
    ·
      refine ⟨32147333200276639333590521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85726221867404371556241389 32147333200276639333590521)
      ·
        refine ⟨24110499900207479500192891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32147333200276639333590521 24110499900207479500192891)
        ·
          refine ⟨36165749850311219250289337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24110499900207479500192891 36165749850311219250289337)
          ·
            refine ⟨27124312387733414437717003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36165749850311219250289337 27124312387733414437717003)
            ·
              refine ⟨40686468581600121656575505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27124312387733414437717003 40686468581600121656575505)
              ·
                refine ⟨30514851436200091242431629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40686468581600121656575505 30514851436200091242431629)
                ·
                  refine ⟨11443069288575034215911861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30514851436200091242431629 11443069288575034215911861)
                  ·
                    refine ⟨1072787745803909457741737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11443069288575034215911861 1072787745803909457741737)
                    ·
                      refine ⟨804590809352932093306303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072787745803909457741737 804590809352932093306303)
                      ·
                        rfl

theorem cell23_1566935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_1566935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566935 prefixEnd_1566935 := by exact prefixLift 1566935
  have htrace : WordTrace (prefixWord ++ tailWord_1566935) baseStart_1566935 baseEnd_1566935 := by
    simpa [prefixWord, tailWord_1566935, baseEnd_1566935] using wordTrace_append hprefix tailTrace_1566935
  have hstable : (prefixWord ++ tailWord_1566935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566935).length < 2 ^ (prefixWord ++ tailWord_1566935).sum := by decide
  have hdescent : baseEnd_1566935 < baseStart_1566935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566936 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 1, 4]
def baseStart_1566936 : Nat := 118140960795 + 1566936 * 2 ^ 59
def prefixEnd_1566936 : Nat := 4983230072969 + 3 ^ 40 * 1566936 * 2
def baseEnd_1566936 : Nat := 268197107611195529797933

theorem tailTrace_1566936 : CollatzResearch.WordTrace tailWord_1566936 prefixEnd_1566936 268197107611195529797933 := by
  unfold tailWord_1566936
  simp only [CollatzResearch.WordTrace]
  refine ⟨28575425525632979104140331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38100567367510638805520441 28575425525632979104140331)
  ·
    refine ⟨42863138288449468656210497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28575425525632979104140331 42863138288449468656210497)
    ·
      refine ⟨32147353716337101492157873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42863138288449468656210497 32147353716337101492157873)
      ·
        refine ⟨24110515287252826119118405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32147353716337101492157873 24110515287252826119118405)
        ·
          refine ⟨4520721616359904897334701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24110515287252826119118405 4520721616359904897334701)
          ·
            refine ⟨1695270606134964336500513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4520721616359904897334701 1695270606134964336500513)
            ·
              refine ⟨1271452954601223252375385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695270606134964336500513 1271452954601223252375385)
              ·
                refine ⟨953589715950917439281539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271452954601223252375385 953589715950917439281539)
                ·
                  refine ⟨1430384573926376158922309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953589715950917439281539 1430384573926376158922309)
                  ·
                    refine ⟨268197107611195529797933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1430384573926376158922309 268197107611195529797933)
                    ·
                      rfl

theorem cell23_1566936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_1566936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566936 prefixEnd_1566936 := by exact prefixLift 1566936
  have htrace : WordTrace (prefixWord ++ tailWord_1566936) baseStart_1566936 baseEnd_1566936 := by
    simpa [prefixWord, tailWord_1566936, baseEnd_1566936] using wordTrace_append hprefix tailTrace_1566936
  have hstable : (prefixWord ++ tailWord_1566936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566936).length < 2 ^ (prefixWord ++ tailWord_1566936).sum := by decide
  have hdescent : baseEnd_1566936 < baseStart_1566936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566975 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 4, 4]
def baseStart_1566975 : Nat := 118140960795 + 1566975 * 2 ^ 59
def prefixEnd_1566975 : Nat := 4983230072969 + 3 ^ 40 * 1566975 * 2
def baseEnd_1566975 : Nat := 268203782859703978935373

theorem tailTrace_1566975 : CollatzResearch.WordTrace tailWord_1566975 prefixEnd_1566975 268203782859703978935373 := by
  unfold tailWord_1566975
  simp only [CollatzResearch.WordTrace]
  refine ⟨57152273498124667868950379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38101515665416445245966919 57152273498124667868950379)
  ·
    refine ⟨85728410247187001803425569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57152273498124667868950379 85728410247187001803425569)
    ·
      refine ⟨64296307685390251352569177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85728410247187001803425569 64296307685390251352569177)
      ·
        refine ⟨48222230764042688514426883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64296307685390251352569177 48222230764042688514426883)
        ·
          refine ⟨72333346146064032771640325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48222230764042688514426883 72333346146064032771640325)
          ·
            refine ⟨13562502402387006144682561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72333346146064032771640325 13562502402387006144682561)
            ·
              refine ⟨10171876801790254608511921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13562502402387006144682561 10171876801790254608511921)
              ·
                refine ⟨7628907601342690956383941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10171876801790254608511921 7628907601342690956383941)
                ·
                  refine ⟨1430420175251754554321989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7628907601342690956383941 1430420175251754554321989)
                  ·
                    refine ⟨268203782859703978935373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1430420175251754554321989 268203782859703978935373)
                    ·
                      rfl

theorem cell23_1566975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_1566975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566975 prefixEnd_1566975 := by exact prefixLift 1566975
  have htrace : WordTrace (prefixWord ++ tailWord_1566975) baseStart_1566975 baseEnd_1566975 := by
    simpa [prefixWord, tailWord_1566975, baseEnd_1566975] using wordTrace_append hprefix tailTrace_1566975
  have hstable : (prefixWord ++ tailWord_1566975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566975).length < 2 ^ (prefixWord ++ tailWord_1566975).sum := by decide
  have hdescent : baseEnd_1566975 < baseStart_1566975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566988 : List Nat := [2, 2, 1, 2, 2, 2, 12]
def baseStart_1566988 : Nat := 118140960795 + 1566988 * 2 ^ 59
def prefixEnd_1566988 : Nat := 4983230072969 + 3 ^ 40 * 1566988 * 2
def baseEnd_1566988 : Nat := 9933555849723708468439

theorem tailTrace_1566988 : CollatzResearch.WordTrace tailWord_1566988 prefixEnd_1566988 9933555849723708468439 := by
  unfold tailWord_1566988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28576373823538785544586809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38101831764718380726115745 28576373823538785544586809)
  ·
    refine ⟨21432280367654089158440107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28576373823538785544586809 21432280367654089158440107)
    ·
      refine ⟨32148420551481133737660161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21432280367654089158440107 32148420551481133737660161)
      ·
        refine ⟨24111315413610850303245121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32148420551481133737660161 24111315413610850303245121)
        ·
          refine ⟨18083486560208137727433841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24111315413610850303245121 18083486560208137727433841)
          ·
            refine ⟨13562614920156103295575381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18083486560208137727433841 13562614920156103295575381)
            ·
              refine ⟨9933555849723708468439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13562614920156103295575381 9933555849723708468439)
              ·
                rfl

theorem cell23_1566988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 12].length) (baseStart_1566988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566988 prefixEnd_1566988 := by exact prefixLift 1566988
  have htrace : WordTrace (prefixWord ++ tailWord_1566988) baseStart_1566988 baseEnd_1566988 := by
    simpa [prefixWord, tailWord_1566988, baseEnd_1566988] using wordTrace_append hprefix tailTrace_1566988
  have hstable : (prefixWord ++ tailWord_1566988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566988).length < 2 ^ (prefixWord ++ tailWord_1566988).sum := by decide
  have hdescent : baseEnd_1566988 < baseStart_1566988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566999 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 3, 2, 2]
def baseStart_1566999 : Nat := 118140960795 + 1566999 * 2 ^ 59
def prefixEnd_1566999 : Nat := 4983230072969 + 3 ^ 40 * 1566999 * 2
def baseEnd_1566999 : Nat := 804623672114819842906009

theorem tailTrace_1566999 : CollatzResearch.WordTrace tailWord_1566999 prefixEnd_1566999 804623672114819842906009 := by
  unfold tailWord_1566999
  simp only [CollatzResearch.WordTrace]
  refine ⟨57153148850037719967824051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38102099233358479978549367 57153148850037719967824051)
  ·
    refine ⟨85729723275056579951736077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57153148850037719967824051 85729723275056579951736077)
    ·
      refine ⟨32148646228146217481901029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85729723275056579951736077 32148646228146217481901029)
      ·
        refine ⟨6027871167777415777856443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32148646228146217481901029 6027871167777415777856443)
        ·
          refine ⟨9041806751666123666784665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027871167777415777856443 9041806751666123666784665)
          ·
            refine ⟨6781355063749592750088499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9041806751666123666784665 6781355063749592750088499)
            ·
              refine ⟨10172032595624389125132749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781355063749592750088499 10172032595624389125132749)
              ·
                refine ⟨3814512223359145921924781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10172032595624389125132749 3814512223359145921924781)
                ·
                  refine ⟨1430442083759679720721793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3814512223359145921924781 1430442083759679720721793)
                  ·
                    refine ⟨1072831562819759790541345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1430442083759679720721793 1072831562819759790541345)
                    ·
                      refine ⟨804623672114819842906009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072831562819759790541345 804623672114819842906009)
                      ·
                        rfl

theorem cell23_1566999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_1566999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1566999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1566999 prefixEnd_1566999 := by exact prefixLift 1566999
  have htrace : WordTrace (prefixWord ++ tailWord_1566999) baseStart_1566999 baseEnd_1566999 := by
    simpa [prefixWord, tailWord_1566999, baseEnd_1566999] using wordTrace_append hprefix tailTrace_1566999
  have hstable : (prefixWord ++ tailWord_1566999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566999).length < 2 ^ (prefixWord ++ tailWord_1566999).sum := by decide
  have hdescent : baseEnd_1566999 < baseStart_1566999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567002 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_1567002 : Nat := 118140960795 + 1567002 * 2 ^ 59
def prefixEnd_1567002 : Nat := 4983230072969 + 3 ^ 40 * 1567002 * 2
def baseEnd_1567002 : Nat := 804625212556783331168495

theorem tailTrace_1567002 : CollatzResearch.WordTrace tailWord_1567002 prefixEnd_1567002 804625212556783331168495 := by
  unfold tailWord_1567002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14288314567256712870045815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38102172179351234320122173 14288314567256712870045815)
  ·
    refine ⟨21432471850885069305068723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14288314567256712870045815 21432471850885069305068723)
    ·
      refine ⟨32148707776327603957603085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21432471850885069305068723 32148707776327603957603085)
      ·
        refine ⟨12055765416122851484101157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32148707776327603957603085 12055765416122851484101157)
        ·
          refine ⟨2260456015523034653268967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12055765416122851484101157 2260456015523034653268967)
          ·
            refine ⟨3390684023284551979903451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260456015523034653268967 3390684023284551979903451)
            ·
              refine ⟨5086026034926827969855177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390684023284551979903451 5086026034926827969855177)
              ·
                refine ⟨3814519526195120977391383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086026034926827969855177 3814519526195120977391383)
                ·
                  refine ⟨5721779289292681466087075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814519526195120977391383 5721779289292681466087075)
                  ·
                    refine ⟨8582668933939022199130613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5721779289292681466087075 8582668933939022199130613)
                    ·
                      refine ⟨804625212556783331168495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8582668933939022199130613 804625212556783331168495)
                      ·
                        rfl

theorem cell23_1567002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_1567002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567002 prefixEnd_1567002 := by exact prefixLift 1567002
  have htrace : WordTrace (prefixWord ++ tailWord_1567002) baseStart_1567002 baseEnd_1567002 := by
    simpa [prefixWord, tailWord_1567002, baseEnd_1567002] using wordTrace_append hprefix tailTrace_1567002
  have hstable : (prefixWord ++ tailWord_1567002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567002).length < 2 ^ (prefixWord ++ tailWord_1567002).sum := by decide
  have hdescent : baseEnd_1567002 < baseStart_1567002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567012 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1567012 : Nat := 118140960795 + 1567012 * 2 ^ 59
def prefixEnd_1567012 : Nat := 4983230072969 + 3 ^ 40 * 1567012 * 2
def baseEnd_1567012 : Nat := 804630347363328292043449

theorem tailTrace_1567012 : CollatzResearch.WordTrace tailWord_1567012 prefixEnd_1567012 804630347363328292043449 := by
  unfold tailWord_1567012
  simp only [CollatzResearch.WordTrace]
  refine ⟨28576811499495311594023645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38102415332660415458698193 28576811499495311594023645)
  ·
    refine ⟨10716304312310741847758867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28576811499495311594023645 10716304312310741847758867)
    ·
      refine ⟨16074456468466112771638301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10716304312310741847758867 16074456468466112771638301)
      ·
        refine ⟨6027921175674792289364363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16074456468466112771638301 6027921175674792289364363)
        ·
          refine ⟨9041881763512188434046545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027921175674792289364363 9041881763512188434046545)
          ·
            refine ⟨6781411322634141325534909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9041881763512188434046545 6781411322634141325534909)
            ·
              refine ⟨2543029245987802997075591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6781411322634141325534909 2543029245987802997075591)
              ·
                refine ⟨3814543868981704495613387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543029245987802997075591 3814543868981704495613387)
                ·
                  refine ⟨5721815803472556743420081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814543868981704495613387 5721815803472556743420081)
                  ·
                    refine ⟨4291361852604417557565061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721815803472556743420081 4291361852604417557565061)
                    ·
                      refine ⟨804630347363328292043449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4291361852604417557565061 804630347363328292043449)
                      ·
                        rfl

theorem cell23_1567012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1567012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567012 prefixEnd_1567012 := by exact prefixLift 1567012
  have htrace : WordTrace (prefixWord ++ tailWord_1567012) baseStart_1567012 baseEnd_1567012 := by
    simpa [prefixWord, tailWord_1567012, baseEnd_1567012] using wordTrace_append hprefix tailTrace_1567012
  have hstable : (prefixWord ++ tailWord_1567012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567012).length < 2 ^ (prefixWord ++ tailWord_1567012).sum := by decide
  have hdescent : baseEnd_1567012 < baseStart_1567012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567032 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_1567032 : Nat := 118140960795 + 1567032 * 2 ^ 59
def prefixEnd_1567032 : Nat := 4983230072969 + 3 ^ 40 * 1567032 * 2
def baseEnd_1567032 : Nat := 804640616976418213793357

theorem tailTrace_1567032 : CollatzResearch.WordTrace tailWord_1567032 prefixEnd_1567032 804640616976418213793357 := by
  unfold tailWord_1567032
  simp only [CollatzResearch.WordTrace]
  refine ⟨28577176229459083301887675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38102901639278777735850233 28577176229459083301887675)
  ·
    refine ⟨42865764344188624952831513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28577176229459083301887675 42865764344188624952831513)
    ·
      refine ⟨32149323258141468714623635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42865764344188624952831513 32149323258141468714623635)
      ·
        refine ⟨48223984887212203071935453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32149323258141468714623635 48223984887212203071935453)
        ·
          refine ⟨18083994332704576151975795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48223984887212203071935453 18083994332704576151975795)
          ·
            refine ⟨27125991499056864227963693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18083994332704576151975795 27125991499056864227963693)
            ·
              refine ⟨10172246812146324085486385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27125991499056864227963693 10172246812146324085486385)
              ·
                refine ⟨7629185109109743064114789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10172246812146324085486385 7629185109109743064114789)
                ·
                  refine ⟨1430472207958076824521523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7629185109109743064114789 1430472207958076824521523)
                  ·
                    refine ⟨2145708311937115236782285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1430472207958076824521523 2145708311937115236782285)
                    ·
                      refine ⟨804640616976418213793357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2145708311937115236782285 804640616976418213793357)
                      ·
                        rfl

theorem cell23_1567032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_1567032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567032 prefixEnd_1567032 := by exact prefixLift 1567032
  have htrace : WordTrace (prefixWord ++ tailWord_1567032) baseStart_1567032 baseEnd_1567032 := by
    simpa [prefixWord, tailWord_1567032, baseEnd_1567032] using wordTrace_append hprefix tailTrace_1567032
  have hstable : (prefixWord ++ tailWord_1567032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567032).length < 2 ^ (prefixWord ++ tailWord_1567032).sum := by decide
  have hdescent : baseEnd_1567032 < baseStart_1567032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567033 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1567033 : Nat := 118140960795 + 1567033 * 2 ^ 59
def prefixEnd_1567033 : Nat := 4983230072969 + 3 ^ 40 * 1567033 * 2
def baseEnd_1567033 : Nat := 804641130457072709880853

theorem tailTrace_1567033 : CollatzResearch.WordTrace tailWord_1567033 prefixEnd_1567033 804641130457072709880853 := by
  unfold tailWord_1567033
  simp only [CollatzResearch.WordTrace]
  refine ⟨57154388931914543774561753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38102925954609695849707835 57154388931914543774561753)
  ·
    refine ⟨42865791698935907830921315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57154388931914543774561753 42865791698935907830921315)
    ·
      refine ⟨64298687548403861746381973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42865791698935907830921315 64298687548403861746381973)
      ·
        refine ⟨3014000978831431019361655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64298687548403861746381973 3014000978831431019361655)
        ·
          refine ⟨4521001468247146529042483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014000978831431019361655 4521001468247146529042483)
          ·
            refine ⟨6781502202370719793563725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521001468247146529042483 6781502202370719793563725)
            ·
              refine ⟨2543063325889019922586397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6781502202370719793563725 2543063325889019922586397)
              ·
                refine ⟨953648747208382470969899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2543063325889019922586397 953648747208382470969899)
                ·
                  refine ⟨1430473120812573706454849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953648747208382470969899 1430473120812573706454849)
                  ·
                    refine ⟨1072854840609430279841137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1430473120812573706454849 1072854840609430279841137)
                    ·
                      refine ⟨804641130457072709880853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072854840609430279841137 804641130457072709880853)
                      ·
                        rfl

theorem cell23_1567033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1567033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567033 prefixEnd_1567033 := by exact prefixLift 1567033
  have htrace : WordTrace (prefixWord ++ tailWord_1567033) baseStart_1567033 baseEnd_1567033 := by
    simpa [prefixWord, tailWord_1567033, baseEnd_1567033] using wordTrace_append hprefix tailTrace_1567033
  have hstable : (prefixWord ++ tailWord_1567033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567033).length < 2 ^ (prefixWord ++ tailWord_1567033).sum := by decide
  have hdescent : baseEnd_1567033 < baseStart_1567033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567070 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1567070 : Nat := 118140960795 + 1567070 * 2 ^ 59
def prefixEnd_1567070 : Nat := 4983230072969 + 3 ^ 40 * 1567070 * 2
def baseEnd_1567070 : Nat := 804660129241289065118183

theorem tailTrace_1567070 : CollatzResearch.WordTrace tailWord_1567070 prefixEnd_1567070 804660129241289065118183 := by
  unfold tailWord_1567070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144467304097562386707333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38103825621853666062439109 7144467304097562386707333)
  ·
    refine ⟨1339587619518292947507625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7144467304097562386707333 1339587619518292947507625)
    ·
      refine ⟨1004690714638719710630719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1339587619518292947507625 1004690714638719710630719)
      ·
        refine ⟨1507036071958079565946079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004690714638719710630719 1507036071958079565946079)
        ·
          refine ⟨2260554107937119348919119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507036071958079565946079 2260554107937119348919119)
          ·
            refine ⟨3390831161905679023378679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260554107937119348919119 3390831161905679023378679)
            ·
              refine ⟨5086246742858518535068019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390831161905679023378679 5086246742858518535068019)
              ·
                refine ⟨7629370114287777802602029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086246742858518535068019 7629370114287777802602029)
                ·
                  refine ⟨2861013792857916675975761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7629370114287777802602029 2861013792857916675975761)
                  ·
                    refine ⟨2145760344643437506981821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861013792857916675975761 2145760344643437506981821)
                    ·
                      refine ⟨804660129241289065118183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2145760344643437506981821 804660129241289065118183)
                      ·
                        rfl

theorem cell23_1567070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1567070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567070 prefixEnd_1567070 := by exact prefixLift 1567070
  have htrace : WordTrace (prefixWord ++ tailWord_1567070) baseStart_1567070 baseEnd_1567070 := by
    simpa [prefixWord, tailWord_1567070, baseEnd_1567070] using wordTrace_append hprefix tailTrace_1567070
  have hstable : (prefixWord ++ tailWord_1567070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567070).length < 2 ^ (prefixWord ++ tailWord_1567070).sum := by decide
  have hdescent : baseEnd_1567070 < baseStart_1567070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567075 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1567075 : Nat := 118140960795 + 1567075 * 2 ^ 59
def prefixEnd_1567075 : Nat := 4983230072969 + 3 ^ 40 * 1567075 * 2
def baseEnd_1567075 : Nat := 804662696644561545555659

theorem tailTrace_1567075 : CollatzResearch.WordTrace tailWord_1567075 prefixEnd_1567075 804662696644561545555659 := by
  unfold tailWord_1567075
  simp only [CollatzResearch.WordTrace]
  refine ⟨57155920797762384947590679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38103947198508256631727119 57155920797762384947590679)
  ·
    refine ⟨85733881196643577421386019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57155920797762384947590679 85733881196643577421386019)
    ·
      refine ⟨128600821794965366132079029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85733881196643577421386019 128600821794965366132079029)
      ·
        refine ⟨12056327043278003074882409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128600821794965366132079029 12056327043278003074882409)
        ·
          refine ⟨9042245282458502306161807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12056327043278003074882409 9042245282458502306161807)
          ·
            refine ⟨13563367923687753459242711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042245282458502306161807 13563367923687753459242711)
            ·
              refine ⟨20345051885531630188864067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13563367923687753459242711 20345051885531630188864067)
              ·
                refine ⟨30517577828297445283296101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20345051885531630188864067 30517577828297445283296101)
                ·
                  refine ⟨5722045842805770990618019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30517577828297445283296101 5722045842805770990618019)
                  ·
                    refine ⟨8583068764208656485927029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5722045842805770990618019 8583068764208656485927029)
                    ·
                      refine ⟨804662696644561545555659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8583068764208656485927029 804662696644561545555659)
                      ·
                        rfl

theorem cell23_1567075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1567075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567075 prefixEnd_1567075 := by exact prefixLift 1567075
  have htrace : WordTrace (prefixWord ++ tailWord_1567075) baseStart_1567075 baseEnd_1567075 := by
    simpa [prefixWord, tailWord_1567075, baseEnd_1567075] using wordTrace_append hprefix tailTrace_1567075
  have hstable : (prefixWord ++ tailWord_1567075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567075).length < 2 ^ (prefixWord ++ tailWord_1567075).sum := by decide
  have hdescent : baseEnd_1567075 < baseStart_1567075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567093 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1567093 : Nat := 118140960795 + 1567093 * 2 ^ 59
def prefixEnd_1567093 : Nat := 4983230072969 + 3 ^ 40 * 1567093 * 2
def baseEnd_1567093 : Nat := 804671939296342475130577

theorem tailTrace_1567093 : CollatzResearch.WordTrace tailWord_1567093 prefixEnd_1567093 804671939296342475130577 := by
  unfold tailWord_1567093
  simp only [CollatzResearch.WordTrace]
  refine ⟨57156577311697174021745933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38104384874464782681163955 57156577311697174021745933)
  ·
    refine ⟨21433716491886440258154725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57156577311697174021745933 21433716491886440258154725)
    ·
      refine ⟨4018821842228707548404011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21433716491886440258154725 4018821842228707548404011)
      ·
        refine ⟨6028232763343061322606017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018821842228707548404011 6028232763343061322606017)
        ·
          refine ⟨4521174572507295991954513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6028232763343061322606017 4521174572507295991954513)
          ·
            refine ⟨3390880929380471993965885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521174572507295991954513 3390880929380471993965885)
            ·
              refine ⟨1271580348517676997737207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3390880929380471993965885 1271580348517676997737207)
              ·
                refine ⟨1907370522776515496605811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271580348517676997737207 1907370522776515496605811)
                ·
                  refine ⟨2861055784164773244908717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907370522776515496605811 2861055784164773244908717)
                  ·
                    refine ⟨1072895919061789966840769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861055784164773244908717 1072895919061789966840769)
                    ·
                      refine ⟨804671939296342475130577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1072895919061789966840769 804671939296342475130577)
                      ·
                        rfl

theorem cell23_1567093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1567093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567093 prefixEnd_1567093 := by exact prefixLift 1567093
  have htrace : WordTrace (prefixWord ++ tailWord_1567093) baseStart_1567093 baseEnd_1567093 := by
    simpa [prefixWord, tailWord_1567093, baseEnd_1567093] using wordTrace_append hprefix tailTrace_1567093
  have hstable : (prefixWord ++ tailWord_1567093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567093).length < 2 ^ (prefixWord ++ tailWord_1567093).sum := by decide
  have hdescent : baseEnd_1567093 < baseStart_1567093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567125 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1567125 : Nat := 118140960795 + 1567125 * 2 ^ 59
def prefixEnd_1567125 : Nat := 4983230072969 + 3 ^ 40 * 1567125 * 2
def baseEnd_1567125 : Nat := 268229456892428783310143

theorem tailTrace_1567125 : CollatzResearch.WordTrace tailWord_1567125 prefixEnd_1567125 268229456892428783310143 := by
  unfold tailWord_1567125
  simp only [CollatzResearch.WordTrace]
  refine ⟨57157744447581243486910829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38105162965054162324607219 57157744447581243486910829)
  ·
    refine ⟨21434154167842966307591561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57157744447581243486910829 21434154167842966307591561)
    ·
      refine ⟨16075615625882224730693671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21434154167842966307591561 16075615625882224730693671)
      ·
        refine ⟨24113423438823337096040507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16075615625882224730693671 24113423438823337096040507)
        ·
          refine ⟨36170135158235005644060761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24113423438823337096040507 36170135158235005644060761)
          ·
            refine ⟨27127601368676254233045571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36170135158235005644060761 27127601368676254233045571)
            ·
              refine ⟨40691402053014381349568357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27127601368676254233045571 40691402053014381349568357)
              ·
                refine ⟨7629637884940196503044067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40691402053014381349568357 7629637884940196503044067)
                ·
                  refine ⟨11444456827410294754566101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7629637884940196503044067 11444456827410294754566101)
                  ·
                    refine ⟨268229456892428783310143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11444456827410294754566101 268229456892428783310143)
                    ·
                      rfl

theorem cell23_1567125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1567125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567125 prefixEnd_1567125 := by exact prefixLift 1567125
  have htrace : WordTrace (prefixWord ++ tailWord_1567125) baseStart_1567125 baseEnd_1567125 := by
    simpa [prefixWord, tailWord_1567125, baseEnd_1567125] using wordTrace_append hprefix tailTrace_1567125
  have hstable : (prefixWord ++ tailWord_1567125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567125).length < 2 ^ (prefixWord ++ tailWord_1567125).sum := by decide
  have hdescent : baseEnd_1567125 < baseStart_1567125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567162 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_1567162 : Nat := 118140960795 + 1567162 * 2 ^ 59
def prefixEnd_1567162 : Nat := 4983230072969 + 3 ^ 40 * 1567162 * 2
def baseEnd_1567162 : Nat := 804707369461502705167759

theorem tailTrace_1567162 : CollatzResearch.WordTrace tailWord_1567162 prefixEnd_1567162 804707369461502705167759 := by
  unfold tailWord_1567162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14289773487111799701501935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38106062632298132537338493 14289773487111799701501935)
  ·
    refine ⟨21434660230667699552252903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14289773487111799701501935 21434660230667699552252903)
    ·
      refine ⟨32151990346001549328379355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21434660230667699552252903 32151990346001549328379355)
      ·
        refine ⟨48227985519002323992569033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32151990346001549328379355 48227985519002323992569033)
        ·
          refine ⟨36170989139251742994426775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48227985519002323992569033 36170989139251742994426775)
          ·
            refine ⟨54256483708877614491640163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36170989139251742994426775 54256483708877614491640163)
            ·
              refine ⟨81384725563316421737460245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54256483708877614491640163 81384725563316421737460245)
              ·
                refine ⟨3814909010780457268943449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81384725563316421737460245 3814909010780457268943449)
                ·
                  refine ⟨2861181758085342951707587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814909010780457268943449 2861181758085342951707587)
                  ·
                    refine ⟨4291772637128014427561381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861181758085342951707587 4291772637128014427561381)
                    ·
                      refine ⟨804707369461502705167759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4291772637128014427561381 804707369461502705167759)
                      ·
                        rfl

theorem cell23_1567162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_1567162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567162 prefixEnd_1567162 := by exact prefixLift 1567162
  have htrace : WordTrace (prefixWord ++ tailWord_1567162) baseStart_1567162 baseEnd_1567162 := by
    simpa [prefixWord, tailWord_1567162, baseEnd_1567162] using wordTrace_append hprefix tailTrace_1567162
  have hstable : (prefixWord ++ tailWord_1567162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567162).length < 2 ^ (prefixWord ++ tailWord_1567162).sum := by decide
  have hdescent : baseEnd_1567162 < baseStart_1567162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567189 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1567189 : Nat := 118140960795 + 1567189 * 2 ^ 59
def prefixEnd_1567189 : Nat := 4983230072969 + 3 ^ 40 * 1567189 * 2
def baseEnd_1567189 : Nat := 268240411146391366510045

theorem tailTrace_1567189 : CollatzResearch.WordTrace tailWord_1567189 prefixEnd_1567189 268240411146391366510045 := by
  unfold tailWord_1567189
  simp only [CollatzResearch.WordTrace]
  refine ⟨57160078719349382417240621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38106719146232921611493747 57160078719349382417240621)
  ·
    refine ⟨21435029519756018406465233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57160078719349382417240621 21435029519756018406465233)
    ·
      refine ⟨16076272139817013804848925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21435029519756018406465233 16076272139817013804848925)
      ·
        refine ⟨6028602052431380176818347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16076272139817013804848925 6028602052431380176818347)
        ·
          refine ⟨9042903078647070265227521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028602052431380176818347 9042903078647070265227521)
          ·
            refine ⟨6782177308985302698920641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9042903078647070265227521 6782177308985302698920641)
            ·
              refine ⟨5086632981738977024190481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6782177308985302698920641 5086632981738977024190481)
              ·
                refine ⟨3814974736304232768142861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086632981738977024190481 3814974736304232768142861)
                ·
                  refine ⟨1430615526114087288053573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3814974736304232768142861 1430615526114087288053573)
                  ·
                    refine ⟨268240411146391366510045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1430615526114087288053573 268240411146391366510045)
                    ·
                      rfl

theorem cell23_1567189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1567189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567189 prefixEnd_1567189 := by exact prefixLift 1567189
  have htrace : WordTrace (prefixWord ++ tailWord_1567189) baseStart_1567189 baseEnd_1567189 := by
    simpa [prefixWord, tailWord_1567189, baseEnd_1567189] using wordTrace_append hprefix tailTrace_1567189
  have hstable : (prefixWord ++ tailWord_1567189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567189).length < 2 ^ (prefixWord ++ tailWord_1567189).sum := by decide
  have hdescent : baseEnd_1567189 < baseStart_1567189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567236 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 6]
def baseStart_1567236 : Nat := 118140960795 + 1567236 * 2 ^ 59
def prefixEnd_1567236 : Nat := 4983230072969 + 3 ^ 40 * 1567236 * 2
def baseEnd_1567236 : Nat := 89416151892215046182491

theorem tailTrace_1567236 : CollatzResearch.WordTrace tailWord_1567236 prefixEnd_1567236 89416151892215046182491 := by
  unfold tailWord_1567236
  simp only [CollatzResearch.WordTrace]
  refine ⟨28580896475089554722100781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38107861966786072962801041 28580896475089554722100781)
  ·
    refine ⟨10717836178158583020787793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28580896475089554722100781 10717836178158583020787793)
    ·
      refine ⟨8038377133618937265590845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10717836178158583020787793 8038377133618937265590845)
      ·
        refine ⟨3014391425107101474596567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8038377133618937265590845 3014391425107101474596567)
        ·
          refine ⟨4521587137660652211894851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014391425107101474596567 4521587137660652211894851)
          ·
            refine ⟨6782380706490978317842277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521587137660652211894851 6782380706490978317842277)
            ·
              refine ⟨1271696382467058434595427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6782380706490978317842277 1271696382467058434595427)
              ·
                refine ⟨1907544573700587651893141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271696382467058434595427 1907544573700587651893141)
                ·
                  refine ⟨89416151892215046182491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1907544573700587651893141 89416151892215046182491)
                  ·
                    rfl

theorem cell23_1567236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_1567236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567236 prefixEnd_1567236 := by exact prefixLift 1567236
  have htrace : WordTrace (prefixWord ++ tailWord_1567236) baseStart_1567236 baseEnd_1567236 := by
    simpa [prefixWord, tailWord_1567236, baseEnd_1567236] using wordTrace_append hprefix tailTrace_1567236
  have hstable : (prefixWord ++ tailWord_1567236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567236).length < 2 ^ (prefixWord ++ tailWord_1567236).sum := by decide
  have hdescent : baseEnd_1567236 < baseStart_1567236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567256 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 2, 3, 2]
def baseStart_1567256 : Nat := 118140960795 + 1567256 * 2 ^ 59
def prefixEnd_1567256 : Nat := 4983230072969 + 3 ^ 40 * 1567256 * 2
def baseEnd_1567256 : Nat := 804755636643025337392327

theorem tailTrace_1567256 : CollatzResearch.WordTrace tailWord_1567256 prefixEnd_1567256 804755636643025337392327 := by
  unfold tailWord_1567256
  simp only [CollatzResearch.WordTrace]
  refine ⟨28581261205053326429964811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38108348273404435239953081 28581261205053326429964811)
  ·
    refine ⟨42871891807579989644947217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28581261205053326429964811 42871891807579989644947217)
    ·
      refine ⟨32153918855684992233710413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42871891807579989644947217 32153918855684992233710413)
      ·
        refine ⟨12057719570881872087641405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32153918855684992233710413 12057719570881872087641405)
        ·
          refine ⟨4521644839080702032865527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12057719570881872087641405 4521644839080702032865527)
          ·
            refine ⟨6782467258621053049298291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521644839080702032865527 6782467258621053049298291)
            ·
              refine ⟨10173700887931579573947437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782467258621053049298291 10173700887931579573947437)
              ·
                refine ⟨3815137832974342340230289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10173700887931579573947437 3815137832974342340230289)
                ·
                  refine ⟨2861353374730756755172717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815137832974342340230289 2861353374730756755172717)
                  ·
                    refine ⟨1073007515524033783189769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861353374730756755172717 1073007515524033783189769)
                    ·
                      refine ⟨804755636643025337392327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073007515524033783189769 804755636643025337392327)
                      ·
                        rfl

theorem cell23_1567256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_1567256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567256 prefixEnd_1567256 := by exact prefixLift 1567256
  have htrace : WordTrace (prefixWord ++ tailWord_1567256) baseStart_1567256 baseEnd_1567256 := by
    simpa [prefixWord, tailWord_1567256, baseEnd_1567256] using wordTrace_append hprefix tailTrace_1567256
  have hstable : (prefixWord ++ tailWord_1567256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567256).length < 2 ^ (prefixWord ++ tailWord_1567256).sum := by decide
  have hdescent : baseEnd_1567256 < baseStart_1567256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567269 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_1567269 : Nat := 118140960795 + 1567269 * 2 ^ 59
def prefixEnd_1567269 : Nat := 4983230072969 + 3 ^ 40 * 1567269 * 2
def baseEnd_1567269 : Nat := 804762311891533786529767

theorem tailTrace_1567269 : CollatzResearch.WordTrace tailWord_1567269 prefixEnd_1567269 804762311891533786529767 := by
  unfold tailWord_1567269
  simp only [CollatzResearch.WordTrace]
  refine ⟨57162996559059556080152861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38108664372706370720101907 57162996559059556080152861)
  ·
    refine ⟨21436123709647333530057323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57162996559059556080152861 21436123709647333530057323)
    ·
      refine ⟨32154185564471000295085985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21436123709647333530057323 32154185564471000295085985)
      ·
        refine ⟨24115639173353250221314489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32154185564471000295085985 24115639173353250221314489)
        ·
          refine ⟨18086729380014937665985867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24115639173353250221314489 18086729380014937665985867)
          ·
            refine ⟨27130094070022406498978801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18086729380014937665985867 27130094070022406498978801)
            ·
              refine ⟨20347570552516804874234101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27130094070022406498978801 20347570552516804874234101)
              ·
                refine ⟨1907584739298450456959447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20347570552516804874234101 1907584739298450456959447)
                ·
                  refine ⟨2861377108947675685439171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907584739298450456959447 2861377108947675685439171)
                  ·
                    refine ⟨4292065663421513528158757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861377108947675685439171 4292065663421513528158757)
                    ·
                      refine ⟨804762311891533786529767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4292065663421513528158757 804762311891533786529767)
                      ·
                        rfl

theorem cell23_1567269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_1567269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567269 prefixEnd_1567269 := by exact prefixLift 1567269
  have htrace : WordTrace (prefixWord ++ tailWord_1567269) baseStart_1567269 baseEnd_1567269 := by
    simpa [prefixWord, tailWord_1567269, baseEnd_1567269] using wordTrace_append hprefix tailTrace_1567269
  have hstable : (prefixWord ++ tailWord_1567269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567269).length < 2 ^ (prefixWord ++ tailWord_1567269).sum := by decide
  have hdescent : baseEnd_1567269 < baseStart_1567269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567282 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1567282 : Nat := 118140960795 + 1567282 * 2 ^ 59
def prefixEnd_1567282 : Nat := 4983230072969 + 3 ^ 40 * 1567282 * 2
def baseEnd_1567282 : Nat := 804768987140042235667207

theorem tailTrace_1567282 : CollatzResearch.WordTrace tailWord_1567282 prefixEnd_1567282 804768987140042235667207 := by
  unfold tailWord_1567282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14290867677003114825094025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38108980472008306200250733 14290867677003114825094025)
  ·
    refine ⟨10718150757752336118820519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14290867677003114825094025 10718150757752336118820519)
    ·
      refine ⟨16077226136628504178230779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718150757752336118820519 16077226136628504178230779)
      ·
        refine ⟨24115839204942756267346169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077226136628504178230779 24115839204942756267346169)
        ·
          refine ⟨18086879403707067200509627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24115839204942756267346169 18086879403707067200509627)
          ·
            refine ⟨27130319105560600800764441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18086879403707067200509627 27130319105560600800764441)
            ·
              refine ⟨20347739329170450600573331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27130319105560600800764441 20347739329170450600573331)
              ·
                refine ⟨30521608993755675900859997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20347739329170450600573331 30521608993755675900859997)
                ·
                  refine ⟨11445603372658378462822499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30521608993755675900859997 11445603372658378462822499)
                  ·
                    refine ⟨17168405058987567694233749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11445603372658378462822499 17168405058987567694233749)
                    ·
                      refine ⟨804768987140042235667207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17168405058987567694233749 804768987140042235667207)
                      ·
                        rfl

theorem cell23_1567282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1567282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567282 prefixEnd_1567282 := by exact prefixLift 1567282
  have htrace : WordTrace (prefixWord ++ tailWord_1567282) baseStart_1567282 baseEnd_1567282 := by
    simpa [prefixWord, tailWord_1567282, baseEnd_1567282] using wordTrace_append hprefix tailTrace_1567282
  have hstable : (prefixWord ++ tailWord_1567282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567282).length < 2 ^ (prefixWord ++ tailWord_1567282).sum := by decide
  have hdescent : baseEnd_1567282 < baseStart_1567282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567286 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1567286 : Nat := 118140960795 + 1567286 * 2 ^ 59
def prefixEnd_1567286 : Nat := 4983230072969 + 3 ^ 40 * 1567286 * 2
def baseEnd_1567286 : Nat := 804771041062660220017189

theorem tailTrace_1567286 : CollatzResearch.WordTrace tailWord_1567286 prefixEnd_1567286 804771041062660220017189 := by
  unfold tailWord_1567286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572726037499872998970107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38109077733331978655681141 3572726037499872998970107)
  ·
    refine ⟨5359089056249809498455161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3572726037499872998970107 5359089056249809498455161)
    ·
      refine ⟨4019316792187357123841371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5359089056249809498455161 4019316792187357123841371)
      ·
        refine ⟨6028975188281035685762057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019316792187357123841371 6028975188281035685762057)
        ·
          refine ⟨4521731391210776764321543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6028975188281035685762057 4521731391210776764321543)
          ·
            refine ⟨6782597086816165146482315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521731391210776764321543 6782597086816165146482315)
            ·
              refine ⟨10173895630224247719723473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782597086816165146482315 10173895630224247719723473)
              ·
                refine ⟨7630421722668185789792605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10173895630224247719723473 7630421722668185789792605)
                ·
                  refine ⟨2861408146000569671172227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7630421722668185789792605 2861408146000569671172227)
                  ·
                    refine ⟨4292112219000854506758341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861408146000569671172227 4292112219000854506758341)
                    ·
                      refine ⟨804771041062660220017189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4292112219000854506758341 804771041062660220017189)
                      ·
                        rfl

theorem cell23_1567286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1567286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567286 prefixEnd_1567286 := by exact prefixLift 1567286
  have htrace : WordTrace (prefixWord ++ tailWord_1567286) baseStart_1567286 baseEnd_1567286 := by
    simpa [prefixWord, tailWord_1567286, baseEnd_1567286] using wordTrace_append hprefix tailTrace_1567286
  have hstable : (prefixWord ++ tailWord_1567286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567286).length < 2 ^ (prefixWord ++ tailWord_1567286).sum := by decide
  have hdescent : baseEnd_1567286 < baseStart_1567286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567289 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1567289 : Nat := 118140960795 + 1567289 * 2 ^ 59
def prefixEnd_1567289 : Nat := 4983230072969 + 3 ^ 40 * 1567289 * 2
def baseEnd_1567289 : Nat := 804772581504623708279675

theorem tailTrace_1567289 : CollatzResearch.WordTrace tailWord_1567289 prefixEnd_1567289 804772581504623708279675 := by
  unfold tailWord_1567289
  simp only [CollatzResearch.WordTrace]
  refine ⟨57163726018987099495880921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38109150679324732997253947 57163726018987099495880921)
  ·
    refine ⟨42872794514240324621910691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57163726018987099495880921 42872794514240324621910691)
    ·
      refine ⟨64309191771360486932866037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42872794514240324621910691 64309191771360486932866037)
      ·
        refine ⟨6028986728565045649956191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64309191771360486932866037 6028986728565045649956191)
        ·
          refine ⟨9043480092847568474934287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028986728565045649956191 9043480092847568474934287)
          ·
            refine ⟨13565220139271352712401431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043480092847568474934287 13565220139271352712401431)
            ·
              refine ⟨20347830208907029068602147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13565220139271352712401431 20347830208907029068602147)
              ·
                refine ⟨30521745313360543602903221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20347830208907029068602147 30521745313360543602903221)
                ·
                  refine ⟨2861413623127550962772177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30521745313360543602903221 2861413623127550962772177)
                  ·
                    refine ⟨2146060217345663222079133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861413623127550962772177 2146060217345663222079133)
                    ·
                      refine ⟨804772581504623708279675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2146060217345663222079133 804772581504623708279675)
                      ·
                        rfl

theorem cell23_1567289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1567289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567289 prefixEnd_1567289 := by exact prefixLift 1567289
  have htrace : WordTrace (prefixWord ++ tailWord_1567289) baseStart_1567289 baseEnd_1567289 := by
    simpa [prefixWord, tailWord_1567289, baseEnd_1567289] using wordTrace_append hprefix tailTrace_1567289
  have hstable : (prefixWord ++ tailWord_1567289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567289).length < 2 ^ (prefixWord ++ tailWord_1567289).sum := by decide
  have hdescent : baseEnd_1567289 < baseStart_1567289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567303 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_1567303 : Nat := 118140960795 + 1567303 * 2 ^ 59
def prefixEnd_1567303 : Nat := 4983230072969 + 3 ^ 40 * 1567303 * 2
def baseEnd_1567303 : Nat := 804779770233786653504611

theorem tailTrace_1567303 : CollatzResearch.WordTrace tailWord_1567303 prefixEnd_1567303 804779770233786653504611 := by
  unfold tailWord_1567303
  simp only [CollatzResearch.WordTrace]
  refine ⟨57164236640936379886890563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38109491093957586591260375 57164236640936379886890563)
  ·
    refine ⟨85746354961404569830335845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57164236640936379886890563 85746354961404569830335845)
    ·
      refine ⟨16077441555263356843187971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85746354961404569830335845 16077441555263356843187971)
      ·
        refine ⟨24116162332895035264781957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077441555263356843187971 24116162332895035264781957)
        ·
          refine ⟨4521780437417819112146617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24116162332895035264781957 4521780437417819112146617)
          ·
            refine ⟨3391335328063364334109963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521780437417819112146617 3391335328063364334109963)
            ·
              refine ⟨5087002992095046501164945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391335328063364334109963 5087002992095046501164945)
              ·
                refine ⟨3815252244071284875873709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087002992095046501164945 3815252244071284875873709)
                ·
                  refine ⟨1430719591526731828452641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3815252244071284875873709 1430719591526731828452641)
                  ·
                    refine ⟨1073039693645048871339481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1430719591526731828452641 1073039693645048871339481)
                    ·
                      refine ⟨804779770233786653504611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073039693645048871339481 804779770233786653504611)
                      ·
                        rfl

theorem cell23_1567303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_1567303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567303 prefixEnd_1567303 := by exact prefixLift 1567303
  have htrace : WordTrace (prefixWord ++ tailWord_1567303) baseStart_1567303 baseEnd_1567303 := by
    simpa [prefixWord, tailWord_1567303, baseEnd_1567303] using wordTrace_append hprefix tailTrace_1567303
  have hstable : (prefixWord ++ tailWord_1567303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567303).length < 2 ^ (prefixWord ++ tailWord_1567303).sum := by decide
  have hdescent : baseEnd_1567303 < baseStart_1567303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567319 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1567319 : Nat := 118140960795 + 1567319 * 2 ^ 59
def prefixEnd_1567319 : Nat := 4983230072969 + 3 ^ 40 * 1567319 * 2
def baseEnd_1567319 : Nat := 804787985924258590904537

theorem tailTrace_1567319 : CollatzResearch.WordTrace tailWord_1567319 prefixEnd_1567319 804787985924258590904537 := by
  unfold tailWord_1567319
  simp only [CollatzResearch.WordTrace]
  refine ⟨57164820208878414619473011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38109880139252276412982007 57164820208878414619473011)
  ·
    refine ⟨85747230313317621929209517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57164820208878414619473011 85747230313317621929209517)
    ·
      refine ⟨32155211367494108223453569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85747230313317621929209517 32155211367494108223453569)
      ·
        refine ⟨24116408525620581167590177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32155211367494108223453569 24116408525620581167590177)
        ·
          refine ⟨18087306394215435875692633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24116408525620581167590177 18087306394215435875692633)
          ·
            refine ⟨13565479795661576906769475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18087306394215435875692633 13565479795661576906769475)
            ·
              refine ⟨20348219693492365360154213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13565479795661576906769475 20348219693492365360154213)
              ·
                refine ⟨3815291192529818505028915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20348219693492365360154213 3815291192529818505028915)
                ·
                  refine ⟨5722936788794727757543373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815291192529818505028915 5722936788794727757543373)
                  ·
                    refine ⟨2146101295798022909078765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5722936788794727757543373 2146101295798022909078765)
                    ·
                      refine ⟨804787985924258590904537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2146101295798022909078765 804787985924258590904537)
                      ·
                        rfl

theorem cell23_1567319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1567319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567319 prefixEnd_1567319 := by exact prefixLift 1567319
  have htrace : WordTrace (prefixWord ++ tailWord_1567319) baseStart_1567319 baseEnd_1567319 := by
    simpa [prefixWord, tailWord_1567319, baseEnd_1567319] using wordTrace_append hprefix tailTrace_1567319
  have hstable : (prefixWord ++ tailWord_1567319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567319).length < 2 ^ (prefixWord ++ tailWord_1567319).sum := by decide
  have hdescent : baseEnd_1567319 < baseStart_1567319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567350 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1567350 : Nat := 118140960795 + 1567350 * 2 ^ 59
def prefixEnd_1567350 : Nat := 4983230072969 + 3 ^ 40 * 1567350 * 2
def baseEnd_1567350 : Nat := 804803903824547969616895

theorem tailTrace_1567350 : CollatzResearch.WordTrace tailWord_1567350 prefixEnd_1567350 804803903824547969616895 := by
  unfold tailWord_1567350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572871929485381682115719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38110633914510737942567669 3572871929485381682115719)
  ·
    refine ⟨5359307894228072523173579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3572871929485381682115719 5359307894228072523173579)
    ·
      refine ⟨8038961841342108784760369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5359307894228072523173579 8038961841342108784760369)
      ·
        refine ⟨6029221381006581588570277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038961841342108784760369 6029221381006581588570277)
        ·
          refine ⟨1130479008938734047856927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6029221381006581588570277 1130479008938734047856927)
          ·
            refine ⟨1695718513408101071785391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130479008938734047856927 1695718513408101071785391)
            ·
              refine ⟨2543577770112151607678087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695718513408101071785391 2543577770112151607678087)
              ·
                refine ⟨3815366655168227411517131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543577770112151607678087 3815366655168227411517131)
                ·
                  refine ⟨5723049982752341117275697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815366655168227411517131 5723049982752341117275697)
                  ·
                    refine ⟨4292287487064255837956773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723049982752341117275697 4292287487064255837956773)
                    ·
                      refine ⟨804803903824547969616895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4292287487064255837956773 804803903824547969616895)
                      ·
                        rfl

theorem cell23_1567350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1567350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567350 prefixEnd_1567350 := by exact prefixLift 1567350
  have htrace : WordTrace (prefixWord ++ tailWord_1567350) baseStart_1567350 baseEnd_1567350 := by
    simpa [prefixWord, tailWord_1567350, baseEnd_1567350] using wordTrace_append hprefix tailTrace_1567350
  have hstable : (prefixWord ++ tailWord_1567350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567350).length < 2 ^ (prefixWord ++ tailWord_1567350).sum := by decide
  have hdescent : baseEnd_1567350 < baseStart_1567350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567380 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1567380 : Nat := 118140960795 + 1567380 * 2 ^ 59
def prefixEnd_1567380 : Nat := 4983230072969 + 3 ^ 40 * 1567380 * 2
def baseEnd_1567380 : Nat := 804819308244182852241757

theorem tailTrace_1567380 : CollatzResearch.WordTrace tailWord_1567380 prefixEnd_1567380 804819308244182852241757 := by
  unfold tailWord_1567380
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583522530828711018721797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38111363374438281358295729 28583522530828711018721797)
  ·
    refine ⟨5359410474530383316010337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28583522530828711018721797 5359410474530383316010337)
    ·
      refine ⟨4019557855897787487007753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5359410474530383316010337 4019557855897787487007753)
      ·
        refine ⟨3014668391923340615255815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4019557855897787487007753 3014668391923340615255815)
        ·
          refine ⟨4522002587885010922883723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014668391923340615255815 4522002587885010922883723)
          ·
            refine ⟨6783003881827516384325585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522002587885010922883723 6783003881827516384325585)
            ·
              refine ⟨5087252911370637288244189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6783003881827516384325585 5087252911370637288244189)
              ·
                refine ⟨1907719841763988983091571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5087252911370637288244189 1907719841763988983091571)
                ·
                  refine ⟨2861579762645983474637357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907719841763988983091571 2861579762645983474637357)
                  ·
                    refine ⟨1073092410992243802989009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861579762645983474637357 1073092410992243802989009)
                    ·
                      refine ⟨804819308244182852241757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073092410992243802989009 804819308244182852241757)
                      ·
                        rfl

theorem cell23_1567380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1567380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567380 prefixEnd_1567380 := by exact prefixLift 1567380
  have htrace : WordTrace (prefixWord ++ tailWord_1567380) baseStart_1567380 baseEnd_1567380 := by
    simpa [prefixWord, tailWord_1567380, baseEnd_1567380] using wordTrace_append hprefix tailTrace_1567380
  have hstable : (prefixWord ++ tailWord_1567380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567380).length < 2 ^ (prefixWord ++ tailWord_1567380).sum := by decide
  have hdescent : baseEnd_1567380 < baseStart_1567380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567389 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1567389 : Nat := 118140960795 + 1567389 * 2 ^ 59
def prefixEnd_1567389 : Nat := 4983230072969 + 3 ^ 40 * 1567389 * 2
def baseEnd_1567389 : Nat := 804823929570073317029215

theorem tailTrace_1567389 : CollatzResearch.WordTrace tailWord_1567389 prefixEnd_1567389 804823929570073317029215 := by
  unfold tailWord_1567389
  simp only [CollatzResearch.WordTrace]
  refine ⟨57167373318624816574521221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38111582212416544383014147 57167373318624816574521221)
  ·
    refine ⟨10718882497242153107722729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57167373318624816574521221 10718882497242153107722729)
    ·
      refine ⟨8039161872931614830792047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10718882497242153107722729 8039161872931614830792047)
      ·
        refine ⟨12058742809397422246188071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8039161872931614830792047 12058742809397422246188071)
        ·
          refine ⟨18088114214096133369282107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12058742809397422246188071 18088114214096133369282107)
          ·
            refine ⟨27132171321144200053923161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18088114214096133369282107 27132171321144200053923161)
            ·
              refine ⟨20349128490858150040442371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27132171321144200053923161 20349128490858150040442371)
              ·
                refine ⟨30523692736287225060663557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20349128490858150040442371 30523692736287225060663557)
                ·
                  refine ⟨5723192388053854698874417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30523692736287225060663557 5723192388053854698874417)
                  ·
                    refine ⟨4292394291040391024155813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723192388053854698874417 4292394291040391024155813)
                    ·
                      refine ⟨804823929570073317029215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4292394291040391024155813 804823929570073317029215)
                      ·
                        rfl

theorem cell23_1567389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1567389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567389 prefixEnd_1567389 := by exact prefixLift 1567389
  have htrace : WordTrace (prefixWord ++ tailWord_1567389) baseStart_1567389 baseEnd_1567389 := by
    simpa [prefixWord, tailWord_1567389, baseEnd_1567389] using wordTrace_append hprefix tailTrace_1567389
  have hstable : (prefixWord ++ tailWord_1567389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567389).length < 2 ^ (prefixWord ++ tailWord_1567389).sum := by decide
  have hdescent : baseEnd_1567389 < baseStart_1567389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567414 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1567414 : Nat := 118140960795 + 1567414 * 2 ^ 59
def prefixEnd_1567414 : Nat := 4983230072969 + 3 ^ 40 * 1567414 * 2
def baseEnd_1567414 : Nat := 804836766586435719216601

theorem tailTrace_1567414 : CollatzResearch.WordTrace tailWord_1567414 prefixEnd_1567414 804836766586435719216601 := by
  unfold tailWord_1567414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573017821470890365261331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38112190095689497229454197 3573017821470890365261331)
  ·
    refine ⟨5359526732206335547891997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573017821470890365261331 5359526732206335547891997)
    ·
      refine ⟨2009822524577375830459499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5359526732206335547891997 2009822524577375830459499)
      ·
        refine ⟨3014733786866063745689249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009822524577375830459499 3014733786866063745689249)
        ·
          refine ⟨2261050340149547809266937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3014733786866063745689249 2261050340149547809266937)
          ·
            refine ⟨1695787755112160856950203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2261050340149547809266937 1695787755112160856950203)
            ·
              refine ⟨2543681632668241285425305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695787755112160856950203 2543681632668241285425305)
              ·
                refine ⟨1907761224501180964068979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2543681632668241285425305 1907761224501180964068979)
                ·
                  refine ⟨2861641836751771446103469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907761224501180964068979 2861641836751771446103469)
                  ·
                    refine ⟨1073115688781914292288801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861641836751771446103469 1073115688781914292288801)
                    ·
                      refine ⟨804836766586435719216601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073115688781914292288801 804836766586435719216601)
                      ·
                        rfl

theorem cell23_1567414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1567414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567414 prefixEnd_1567414 := by exact prefixLift 1567414
  have htrace : WordTrace (prefixWord ++ tailWord_1567414) baseStart_1567414 baseEnd_1567414 := by
    simpa [prefixWord, tailWord_1567414, baseEnd_1567414] using wordTrace_append hprefix tailTrace_1567414
  have hstable : (prefixWord ++ tailWord_1567414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567414).length < 2 ^ (prefixWord ++ tailWord_1567414).sum := by decide
  have hdescent : baseEnd_1567414 < baseStart_1567414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567489 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 8]
def baseStart_1567489 : Nat := 118140960795 + 1567489 * 2 ^ 59
def prefixEnd_1567489 : Nat := 4983230072969 + 3 ^ 40 * 1567489 * 2
def baseEnd_1567489 : Nat := 89430586403946991753195

theorem tailTrace_1567489 : CollatzResearch.WordTrace tailWord_1567489 prefixEnd_1567489 89430586403946991753195 := by
  unfold tailWord_1567489
  simp only [CollatzResearch.WordTrace]
  refine ⟨57171020618262533653161521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38114013745508355768774347 57171020618262533653161521)
  ·
    refine ⟨42878265463696900239871141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57171020618262533653161521 42878265463696900239871141)
    ·
      refine ⟨8039674774443168794975839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42878265463696900239871141 8039674774443168794975839)
      ·
        refine ⟨12059512161664753192463759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8039674774443168794975839 12059512161664753192463759)
        ·
          refine ⟨18089268242497129788695639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12059512161664753192463759 18089268242497129788695639)
          ·
            refine ⟨27133902363745694683043459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18089268242497129788695639 27133902363745694683043459)
            ·
              refine ⟨40700853545618542024565189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27133902363745694683043459 40700853545618542024565189)
              ·
                refine ⟨7631410039803476629605973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40700853545618542024565189 7631410039803476629605973)
                ·
                  refine ⟨89430586403946991753195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7631410039803476629605973 89430586403946991753195)
                  ·
                    rfl

theorem cell23_1567489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_1567489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567489 prefixEnd_1567489 := by exact prefixLift 1567489
  have htrace : WordTrace (prefixWord ++ tailWord_1567489) baseStart_1567489 baseEnd_1567489 := by
    simpa [prefixWord, tailWord_1567489, baseEnd_1567489] using wordTrace_append hprefix tailTrace_1567489
  have hstable : (prefixWord ++ tailWord_1567489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567489).length < 2 ^ (prefixWord ++ tailWord_1567489).sum := by decide
  have hdescent : baseEnd_1567489 < baseStart_1567489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567509 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1567509 : Nat := 118140960795 + 1567509 * 2 ^ 59
def prefixEnd_1567509 : Nat := 4983230072969 + 3 ^ 40 * 1567509 * 2
def baseEnd_1567509 : Nat := 804885547248612847528663

theorem tailTrace_1567509 : CollatzResearch.WordTrace tailWord_1567509 prefixEnd_1567509 804885547248612847528663 := by
  unfold tailWord_1567509
  simp only [CollatzResearch.WordTrace]
  refine ⟨57171750078190077068889581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38114500052126718045926387 57171750078190077068889581)
  ·
    refine ⟨21439406279321278900833593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57171750078190077068889581 21439406279321278900833593)
    ·
      refine ⟨16079554709490959175625195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21439406279321278900833593 16079554709490959175625195)
      ·
        refine ⟨24119332064236438763437793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16079554709490959175625195 24119332064236438763437793)
        ·
          refine ⟨18089499048177329072578345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24119332064236438763437793 18089499048177329072578345)
          ·
            refine ⟨13567124286132996804433759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18089499048177329072578345 13567124286132996804433759)
            ·
              refine ⟨20350686429199495206650639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13567124286132996804433759 20350686429199495206650639)
              ·
                refine ⟨30526029643799242809975959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20350686429199495206650639 30526029643799242809975959)
                ·
                  refine ⟨45789044465698864214963939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30526029643799242809975959 45789044465698864214963939)
                  ·
                    refine ⟨68683566698548296322445909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45789044465698864214963939 68683566698548296322445909)
                    ·
                      refine ⟨804885547248612847528663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68683566698548296322445909 804885547248612847528663)
                      ·
                        rfl

theorem cell23_1567509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1567509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567509 prefixEnd_1567509 := by exact prefixLift 1567509
  have htrace : WordTrace (prefixWord ++ tailWord_1567509) baseStart_1567509 baseEnd_1567509 := by
    simpa [prefixWord, tailWord_1567509, baseEnd_1567509] using wordTrace_append hprefix tailTrace_1567509
  have hstable : (prefixWord ++ tailWord_1567509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567509).length < 2 ^ (prefixWord ++ tailWord_1567509).sum := by decide
  have hdescent : baseEnd_1567509 < baseStart_1567509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567543 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 2, 3, 2]
def baseStart_1567543 : Nat := 118140960795 + 1567543 * 2 ^ 59
def prefixEnd_1567543 : Nat := 4983230072969 + 3 ^ 40 * 1567543 * 2
def baseEnd_1567543 : Nat := 804903005590865714503507

theorem tailTrace_1567543 : CollatzResearch.WordTrace tailWord_1567543 prefixEnd_1567543 804903005590865714503507 := by
  unfold tailWord_1567543
  simp only [CollatzResearch.WordTrace]
  refine ⟨57172990160066900875627283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38115326773377933917084855 57172990160066900875627283)
  ·
    refine ⟨85759485240100351313440925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57172990160066900875627283 85759485240100351313440925)
    ·
      refine ⟨32159806965037631742540347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85759485240100351313440925 32159806965037631742540347)
      ·
        refine ⟨48239710447556447613810521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32159806965037631742540347 48239710447556447613810521)
        ·
          refine ⟨36179782835667335710357891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48239710447556447613810521 36179782835667335710357891)
          ·
            refine ⟨54269674253501003565536837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36179782835667335710357891 54269674253501003565536837)
            ·
              refine ⟨10175563922531438168538157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54269674253501003565536837 10175563922531438168538157)
              ·
                refine ⟨3815836470949289313201809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10175563922531438168538157 3815836470949289313201809)
                ·
                  refine ⟨2861877353211966984901357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815836470949289313201809 2861877353211966984901357)
                  ·
                    refine ⟨1073204007454487619338009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2861877353211966984901357 1073204007454487619338009)
                    ·
                      refine ⟨804903005590865714503507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073204007454487619338009 804903005590865714503507)
                      ·
                        rfl

theorem cell23_1567543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_1567543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567543 prefixEnd_1567543 := by exact prefixLift 1567543
  have htrace : WordTrace (prefixWord ++ tailWord_1567543) baseStart_1567543 baseEnd_1567543 := by
    simpa [prefixWord, tailWord_1567543, baseEnd_1567543] using wordTrace_append hprefix tailTrace_1567543
  have hstable : (prefixWord ++ tailWord_1567543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567543).length < 2 ^ (prefixWord ++ tailWord_1567543).sum := by decide
  have hdescent : baseEnd_1567543 < baseStart_1567543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567583 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 2, 4]
def baseStart_1567583 : Nat := 118140960795 + 1567583 * 2 ^ 59
def prefixEnd_1567583 : Nat := 4983230072969 + 3 ^ 40 * 1567583 * 2
def baseEnd_1567583 : Nat := 268307848272348519334441

theorem tailTrace_1567583 : CollatzResearch.WordTrace tailWord_1567583 prefixEnd_1567583 268307848272348519334441 := by
  unfold tailWord_1567583
  simp only [CollatzResearch.WordTrace]
  refine ⟨57174449079921987707083403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38116299386614658471388935 57174449079921987707083403)
  ·
    refine ⟨85761673619882981560625105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57174449079921987707083403 85761673619882981560625105)
    ·
      refine ⟨64321255214912236170468829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85761673619882981560625105 64321255214912236170468829)
      ·
        refine ⟨24120470705592088563925811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64321255214912236170468829 24120470705592088563925811)
        ·
          refine ⟨36180706058388132845888717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120470705592088563925811 36180706058388132845888717)
          ·
            refine ⟨13567764771895549817208269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36180706058388132845888717 13567764771895549817208269)
            ·
              refine ⟨5087911789460831181453101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13567764771895549817208269 5087911789460831181453101)
              ·
                refine ⟨1907966921047811693044913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5087911789460831181453101 1907966921047811693044913)
                ·
                  refine ⟨1430975190785858769783685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1907966921047811693044913 1430975190785858769783685)
                  ·
                    refine ⟨268307848272348519334441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1430975190785858769783685 268307848272348519334441)
                    ·
                      rfl

theorem cell23_1567583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_1567583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567583 prefixEnd_1567583 := by exact prefixLift 1567583
  have htrace : WordTrace (prefixWord ++ tailWord_1567583) baseStart_1567583 baseEnd_1567583 := by
    simpa [prefixWord, tailWord_1567583, baseEnd_1567583] using wordTrace_append hprefix tailTrace_1567583
  have hstable : (prefixWord ++ tailWord_1567583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567583).length < 2 ^ (prefixWord ++ tailWord_1567583).sum := by decide
  have hdescent : baseEnd_1567583 < baseStart_1567583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567624 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1567624 : Nat := 118140960795 + 1567624 * 2 ^ 59
def prefixEnd_1567624 : Nat := 4983230072969 + 3 ^ 40 * 1567624 * 2
def baseEnd_1567624 : Nat := 804944597523879897590635

theorem tailTrace_1567624 : CollatzResearch.WordTrace tailWord_1567624 prefixEnd_1567624 804944597523879897590635 := by
  unfold tailWord_1567624
  simp only [CollatzResearch.WordTrace]
  refine ⟨28587972236386725854662963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38117296315182301139550617 28587972236386725854662963)
  ·
    refine ⟨42881958354580088781994445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28587972236386725854662963 42881958354580088781994445)
    ·
      refine ⟨16080734382967533293247917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42881958354580088781994445 16080734382967533293247917)
      ·
        refine ⟨6030275393612824984967969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16080734382967533293247917 6030275393612824984967969)
        ·
          refine ⟨4522706545209618738725977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6030275393612824984967969 4522706545209618738725977)
          ·
            refine ⟨3392029908907214054044483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4522706545209618738725977 3392029908907214054044483)
            ·
              refine ⟨5088044863360821081066725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392029908907214054044483 5088044863360821081066725)
              ·
                refine ⟨954008411880153952700011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5088044863360821081066725 954008411880153952700011)
                ·
                  refine ⟨1431012617820230929050017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954008411880153952700011 1431012617820230929050017)
                  ·
                    refine ⟨1073259463365173196787513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431012617820230929050017 1073259463365173196787513)
                    ·
                      refine ⟨804944597523879897590635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073259463365173196787513 804944597523879897590635)
                      ·
                        rfl

theorem cell23_1567624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1567624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567624 prefixEnd_1567624 := by exact prefixLift 1567624
  have htrace : WordTrace (prefixWord ++ tailWord_1567624) baseStart_1567624 baseEnd_1567624 := by
    simpa [prefixWord, tailWord_1567624, baseEnd_1567624] using wordTrace_append hprefix tailTrace_1567624
  have hstable : (prefixWord ++ tailWord_1567624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567624).length < 2 ^ (prefixWord ++ tailWord_1567624).sum := by decide
  have hdescent : baseEnd_1567624 < baseStart_1567624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567661 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1567661 : Nat := 118140960795 + 1567661 * 2 ^ 59
def prefixEnd_1567661 : Nat := 4983230072969 + 3 ^ 40 * 1567661 * 2
def baseEnd_1567661 : Nat := 804963596308096252827965

theorem tailTrace_1567661 : CollatzResearch.WordTrace tailWord_1567661 prefixEnd_1567661 804963596308096252827965 := by
  unfold tailWord_1567661
  simp only [CollatzResearch.WordTrace]
  refine ⟨57177293973639407028422837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38118195982426271352281891 57177293973639407028422837)
  ·
    refine ⟨5360371310028694408914641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57177293973639407028422837 5360371310028694408914641)
    ·
      refine ⟨4020278482521520806685981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5360371310028694408914641 4020278482521520806685981)
      ·
        refine ⟨1507604430945570302507243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4020278482521520806685981 1507604430945570302507243)
        ·
          refine ⟨2261406646418355453760865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507604430945570302507243 2261406646418355453760865)
          ·
            refine ⟨1696054984813766590320649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2261406646418355453760865 1696054984813766590320649)
            ·
              refine ⟨1272041238610324942740487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696054984813766590320649 1272041238610324942740487)
              ·
                refine ⟨1908061857915487414110731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272041238610324942740487 1908061857915487414110731)
                ·
                  refine ⟨2862092786873231121166097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908061857915487414110731 2862092786873231121166097)
                  ·
                    refine ⟨2146569590154923340874573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2862092786873231121166097 2146569590154923340874573)
                    ·
                      refine ⟨804963596308096252827965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2146569590154923340874573 804963596308096252827965)
                      ·
                        rfl

theorem cell23_1567661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1567661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567661 prefixEnd_1567661 := by exact prefixLift 1567661
  have htrace : WordTrace (prefixWord ++ tailWord_1567661) baseStart_1567661 baseEnd_1567661 := by
    simpa [prefixWord, tailWord_1567661, baseEnd_1567661] using wordTrace_append hprefix tailTrace_1567661
  have hstable : (prefixWord ++ tailWord_1567661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567661).length < 2 ^ (prefixWord ++ tailWord_1567661).sum := by decide
  have hdescent : baseEnd_1567661 < baseStart_1567661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567663 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 3, 4, 2]
def baseStart_1567663 : Nat := 118140960795 + 1567663 * 2 ^ 59
def prefixEnd_1567663 : Nat := 4983230072969 + 3 ^ 40 * 1567663 * 2
def baseEnd_1567663 : Nat := 804964623269405245002955

theorem tailTrace_1567663 : CollatzResearch.WordTrace tailWord_1567663 prefixEnd_1567663 804964623269405245002955 := by
  unfold tailWord_1567663
  simp only [CollatzResearch.WordTrace]
  refine ⟨57177366919632161369995643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38118244613088107579997095 57177366919632161369995643)
  ·
    refine ⟨85766050379448242054993465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57177366919632161369995643 85766050379448242054993465)
    ·
      refine ⟨64324537784586181541245099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85766050379448242054993465 64324537784586181541245099)
      ·
        refine ⟨96486806676879272311867649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64324537784586181541245099 96486806676879272311867649)
        ·
          refine ⟨72365105007659454233900737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96486806676879272311867649 72365105007659454233900737)
          ·
            refine ⟨54273828755744590675425553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72365105007659454233900737 54273828755744590675425553)
            ·
              refine ⟨40705371566808443006569165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54273828755744590675425553 40705371566808443006569165)
              ·
                refine ⟨15264514337553166127463437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40705371566808443006569165 15264514337553166127463437)
                ·
                  refine ⟨5724192876582437297798789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15264514337553166127463437 5724192876582437297798789)
                  ·
                    refine ⟨1073286164359206993337273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724192876582437297798789 1073286164359206993337273)
                    ·
                      refine ⟨804964623269405245002955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073286164359206993337273 804964623269405245002955)
                      ·
                        rfl

theorem cell23_1567663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4, 2].length) (baseStart_1567663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567663 prefixEnd_1567663 := by exact prefixLift 1567663
  have htrace : WordTrace (prefixWord ++ tailWord_1567663) baseStart_1567663 baseEnd_1567663 := by
    simpa [prefixWord, tailWord_1567663, baseEnd_1567663] using wordTrace_append hprefix tailTrace_1567663
  have hstable : (prefixWord ++ tailWord_1567663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567663).length < 2 ^ (prefixWord ++ tailWord_1567663).sum := by decide
  have hdescent : baseEnd_1567663 < baseStart_1567663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567714 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1567714 : Nat := 118140960795 + 1567714 * 2 ^ 59
def prefixEnd_1567714 : Nat := 4983230072969 + 3 ^ 40 * 1567714 * 2
def baseEnd_1567714 : Nat := 804990810782784545465221

theorem tailTrace_1567714 : CollatzResearch.WordTrace tailWord_1567714 prefixEnd_1567714 804990810782784545465221 := by
  unfold tailWord_1567714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14294806760611849270025549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38119484694964931386734797 14294806760611849270025549)
  ·
    refine ⟨5360552535229443476259581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14294806760611849270025549 5360552535229443476259581)
    ·
      refine ⟨2010207200711041303597343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5360552535229443476259581 2010207200711041303597343)
      ·
        refine ⟨3015310801066561955396015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010207200711041303597343 3015310801066561955396015)
        ·
          refine ⟨4522966201599842933094023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015310801066561955396015 4522966201599842933094023)
          ·
            refine ⟨6784449302399764399641035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522966201599842933094023 6784449302399764399641035)
            ·
              refine ⟨10176673953599646599461553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784449302399764399641035 10176673953599646599461553)
              ·
                refine ⟨7632505465199734949596165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10176673953599646599461553 7632505465199734949596165)
                ·
                  refine ⟨1431094774724950303049281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7632505465199734949596165 1431094774724950303049281)
                  ·
                    refine ⟨1073321081043712727286961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431094774724950303049281 1073321081043712727286961)
                    ·
                      refine ⟨804990810782784545465221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073321081043712727286961 804990810782784545465221)
                      ·
                        rfl

theorem cell23_1567714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1567714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567714 prefixEnd_1567714 := by exact prefixLift 1567714
  have htrace : WordTrace (prefixWord ++ tailWord_1567714) baseStart_1567714 baseEnd_1567714 := by
    simpa [prefixWord, tailWord_1567714, baseEnd_1567714] using wordTrace_append hprefix tailTrace_1567714
  have hstable : (prefixWord ++ tailWord_1567714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567714).length < 2 ^ (prefixWord ++ tailWord_1567714).sum := by decide
  have hdescent : baseEnd_1567714 < baseStart_1567714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567720 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 5]
def baseStart_1567720 : Nat := 118140960795 + 1567720 * 2 ^ 59
def prefixEnd_1567720 : Nat := 4983230072969 + 3 ^ 40 * 1567720 * 2
def baseEnd_1567720 : Nat := 89443765740745724665577

theorem tailTrace_1567720 : CollatzResearch.WordTrace tailWord_1567720 prefixEnd_1567720 89443765740745724665577 := by
  unfold tailWord_1567720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28589722940212830052410307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38119630586950440069880409 28589722940212830052410307)
  ·
    refine ⟨42884584410319245078615461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28589722940212830052410307 42884584410319245078615461)
    ·
      refine ⟨8040859576934858452240399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42884584410319245078615461 8040859576934858452240399)
      ·
        refine ⟨12061289365402287678360599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040859576934858452240399 12061289365402287678360599)
        ·
          refine ⟨18091934048103431517540899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061289365402287678360599 18091934048103431517540899)
          ·
            refine ⟨27137901072155147276311349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18091934048103431517540899 27137901072155147276311349)
            ·
              refine ⟨2544178225514545057154189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27137901072155147276311349 2544178225514545057154189)
              ·
                refine ⟨954066834567954396432821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2544178225514545057154189 954066834567954396432821)
                ·
                  refine ⟨89443765740745724665577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 954066834567954396432821 89443765740745724665577)
                  ·
                    rfl

theorem cell23_1567720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 5].length) (baseStart_1567720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567720 prefixEnd_1567720 := by exact prefixLift 1567720
  have htrace : WordTrace (prefixWord ++ tailWord_1567720) baseStart_1567720 baseEnd_1567720 := by
    simpa [prefixWord, tailWord_1567720, baseEnd_1567720] using wordTrace_append hprefix tailTrace_1567720
  have hstable : (prefixWord ++ tailWord_1567720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567720).length < 2 ^ (prefixWord ++ tailWord_1567720).sum := by decide
  have hdescent : baseEnd_1567720 < baseStart_1567720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567723 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 7, 2]
def baseStart_1567723 : Nat := 118140960795 + 1567723 * 2 ^ 59
def prefixEnd_1567723 : Nat := 4983230072969 + 3 ^ 40 * 1567723 * 2
def baseEnd_1567723 : Nat := 804995432108675010252679

theorem tailTrace_1567723 : CollatzResearch.WordTrace tailWord_1567723 prefixEnd_1567723 804995432108675010252679 := by
  unfold tailWord_1567723
  simp only [CollatzResearch.WordTrace]
  refine ⟨57179555299414791617179823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38119703532943194411453215 57179555299414791617179823)
  ·
    refine ⟨85769332949122187425769735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57179555299414791617179823 85769332949122187425769735)
    ·
      refine ⟨128653999423683281138654603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85769332949122187425769735 128653999423683281138654603)
      ·
        refine ⟨192980999135524921707981905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128653999423683281138654603 192980999135524921707981905)
        ·
          refine ⟨144735749351643691280986429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192980999135524921707981905 144735749351643691280986429)
          ·
            refine ⟨54275906006866384230369911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144735749351643691280986429 54275906006866384230369911)
            ·
              refine ⟨81413859010299576345554867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54275906006866384230369911 81413859010299576345554867)
              ·
                refine ⟨122120788515449364518332301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81413859010299576345554867 122120788515449364518332301)
                ·
                  refine ⟨45795295693293511694374613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122120788515449364518332301 45795295693293511694374613)
                  ·
                    refine ⟨1073327242811566680336905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45795295693293511694374613 1073327242811566680336905)
                    ·
                      refine ⟨804995432108675010252679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073327242811566680336905 804995432108675010252679)
                      ·
                        rfl

theorem cell23_1567723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7, 2].length) (baseStart_1567723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567723 prefixEnd_1567723 := by exact prefixLift 1567723
  have htrace : WordTrace (prefixWord ++ tailWord_1567723) baseStart_1567723 baseEnd_1567723 := by
    simpa [prefixWord, tailWord_1567723, baseEnd_1567723] using wordTrace_append hprefix tailTrace_1567723
  have hstable : (prefixWord ++ tailWord_1567723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567723).length < 2 ^ (prefixWord ++ tailWord_1567723).sum := by decide
  have hdescent : baseEnd_1567723 < baseStart_1567723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567763 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 5, 4]
def baseStart_1567763 : Nat := 118140960795 + 1567763 * 2 ^ 59
def prefixEnd_1567763 : Nat := 4983230072969 + 3 ^ 40 * 1567763 * 2
def baseEnd_1567763 : Nat := 268338657111618284584165

theorem tailTrace_1567763 : CollatzResearch.WordTrace tailWord_1567763 prefixEnd_1567763 268338657111618284584165 := by
  unfold tailWord_1567763
  simp only [CollatzResearch.WordTrace]
  refine ⟨57181014219269878448635943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38120676146179918965757295 57181014219269878448635943)
  ·
    refine ⟨85771521328904817672953915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57181014219269878448635943 85771521328904817672953915)
    ·
      refine ⟨128657281993357226509430873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85771521328904817672953915 128657281993357226509430873)
      ·
        refine ⟨96492961495017919882073155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128657281993357226509430873 96492961495017919882073155)
        ·
          refine ⟨144739442242526879823109733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96492961495017919882073155 144739442242526879823109733)
          ·
            refine ⟨27138645420473789966833075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144739442242526879823109733 27138645420473789966833075)
            ·
              refine ⟨40707968130710684950249613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138645420473789966833075 40707968130710684950249613)
              ·
                refine ⟨15265488049016506856343605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40707968130710684950249613 15265488049016506856343605)
                ·
                  refine ⟨1431139504595297517782213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15265488049016506856343605 1431139504595297517782213)
                  ·
                    refine ⟨268338657111618284584165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431139504595297517782213 268338657111618284584165)
                    ·
                      rfl

theorem cell23_1567763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 4].length) (baseStart_1567763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567763 prefixEnd_1567763 := by exact prefixLift 1567763
  have htrace : WordTrace (prefixWord ++ tailWord_1567763) baseStart_1567763 baseEnd_1567763 := by
    simpa [prefixWord, tailWord_1567763, baseEnd_1567763] using wordTrace_append hprefix tailTrace_1567763
  have hstable : (prefixWord ++ tailWord_1567763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567763).length < 2 ^ (prefixWord ++ tailWord_1567763).sum := by decide
  have hdescent : baseEnd_1567763 < baseStart_1567763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567770 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_1567770 : Nat := 118140960795 + 1567770 * 2 ^ 59
def prefixEnd_1567770 : Nat := 4983230072969 + 3 ^ 40 * 1567770 * 2
def baseEnd_1567770 : Nat := 805019565699436326364963

theorem tailTrace_1567770 : CollatzResearch.WordTrace tailWord_1567770 prefixEnd_1567770 805019565699436326364963 := by
  unfold tailWord_1567770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14295317382561129661035191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38120846353496345762760509 14295317382561129661035191)
  ·
    refine ⟨21442976073841694491552787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14295317382561129661035191 21442976073841694491552787)
    ·
      refine ⟨32164464110762541737329181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21442976073841694491552787 32164464110762541737329181)
      ·
        refine ⟨12061674041535953151498443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32164464110762541737329181 12061674041535953151498443)
        ·
          refine ⟨18092511062303929727247665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061674041535953151498443 18092511062303929727247665)
          ·
            refine ⟨13569383296727947295435749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18092511062303929727247665 13569383296727947295435749)
            ·
              refine ⟨2544259368136490117894203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13569383296727947295435749 2544259368136490117894203)
              ·
                refine ⟨3816389052204735176841305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544259368136490117894203 3816389052204735176841305)
                ·
                  refine ⟨2862291789153551382630979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816389052204735176841305 2862291789153551382630979)
                  ·
                    refine ⟨4293437683730327073946469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2862291789153551382630979 4293437683730327073946469)
                    ·
                      refine ⟨805019565699436326364963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4293437683730327073946469 805019565699436326364963)
                      ·
                        rfl

theorem cell23_1567770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_1567770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567770 prefixEnd_1567770 := by exact prefixLift 1567770
  have htrace : WordTrace (prefixWord ++ tailWord_1567770) baseStart_1567770 baseEnd_1567770 := by
    simpa [prefixWord, tailWord_1567770, baseEnd_1567770] using wordTrace_append hprefix tailTrace_1567770
  have hstable : (prefixWord ++ tailWord_1567770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567770).length < 2 ^ (prefixWord ++ tailWord_1567770).sum := by decide
  have hdescent : baseEnd_1567770 < baseStart_1567770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567814 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1567814 : Nat := 118140960795 + 1567814 * 2 ^ 59
def prefixEnd_1567814 : Nat := 4983230072969 + 3 ^ 40 * 1567814 * 2
def baseEnd_1567814 : Nat := 268347386282744718071587

theorem tailTrace_1567814 : CollatzResearch.WordTrace tailWord_1567814 prefixEnd_1567814 268347386282744718071587 := by
  unfold tailWord_1567814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786964823190159817460703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38121916228056742772494997 1786964823190159817460703)
  ·
    refine ⟨2680447234785239726191055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786964823190159817460703 2680447234785239726191055)
    ·
      refine ⟨4020670852177859589286583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680447234785239726191055 4020670852177859589286583)
      ·
        refine ⟨6031006278266789383929875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020670852177859589286583 6031006278266789383929875)
        ·
          refine ⟨9046509417400184075894813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031006278266789383929875 9046509417400184075894813)
          ·
            refine ⟨3392441031525069028460555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9046509417400184075894813 3392441031525069028460555)
            ·
              refine ⟨5088661547287603542690833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392441031525069028460555 5088661547287603542690833)
              ·
                refine ⟨3816496160465702657018125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088661547287603542690833 3816496160465702657018125)
                ·
                  refine ⟨1431186060174638496381797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3816496160465702657018125 1431186060174638496381797)
                  ·
                    refine ⟨268347386282744718071587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431186060174638496381797 268347386282744718071587)
                    ·
                      rfl

theorem cell23_1567814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1567814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567814 prefixEnd_1567814 := by exact prefixLift 1567814
  have htrace : WordTrace (prefixWord ++ tailWord_1567814) baseStart_1567814 baseEnd_1567814 := by
    simpa [prefixWord, tailWord_1567814, baseEnd_1567814] using wordTrace_append hprefix tailTrace_1567814
  have hstable : (prefixWord ++ tailWord_1567814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567814).length < 2 ^ (prefixWord ++ tailWord_1567814).sum := by decide
  have hdescent : baseEnd_1567814 < baseStart_1567814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567840 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 1, 5]
def baseStart_1567840 : Nat := 118140960795 + 1567840 * 2 ^ 59
def prefixEnd_1567840 : Nat := 4983230072969 + 3 ^ 40 * 1567840 * 2
def baseEnd_1567840 : Nat := 268351836448417017496547

theorem tailTrace_1567840 : CollatzResearch.WordTrace tailWord_1567840 prefixEnd_1567840 268351836448417017496547 := by
  unfold tailWord_1567840
  simp only [CollatzResearch.WordTrace]
  refine ⟨28591911319995460299594487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38122548426660613732792649 28591911319995460299594487)
  ·
    refine ⟨42887866979993190449391731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28591911319995460299594487 42887866979993190449391731)
    ·
      refine ⟨64331800469989785674087597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42887866979993190449391731 64331800469989785674087597)
      ·
        refine ⟨24124425176246169627782849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64331800469989785674087597 24124425176246169627782849)
        ·
          refine ⟨18093318882184627220837137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24124425176246169627782849 18093318882184627220837137)
          ·
            refine ⟨13569989161638470415627853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18093318882184627220837137 13569989161638470415627853)
            ·
              refine ⟨5088745935614426405860445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13569989161638470415627853 5088745935614426405860445)
              ·
                refine ⟨1908279725855409902197667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5088745935614426405860445 1908279725855409902197667)
                ·
                  refine ⟨2862419588783114853296501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908279725855409902197667 2862419588783114853296501)
                  ·
                    refine ⟨268351836448417017496547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2862419588783114853296501 268351836448417017496547)
                    ·
                      rfl

theorem cell23_1567840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_1567840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567840 prefixEnd_1567840 := by exact prefixLift 1567840
  have htrace : WordTrace (prefixWord ++ tailWord_1567840) baseStart_1567840 baseEnd_1567840 := by
    simpa [prefixWord, tailWord_1567840, baseEnd_1567840] using wordTrace_append hprefix tailTrace_1567840
  have hstable : (prefixWord ++ tailWord_1567840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567840).length < 2 ^ (prefixWord ++ tailWord_1567840).sum := by decide
  have hdescent : baseEnd_1567840 < baseStart_1567840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567854 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1567854 : Nat := 118140960795 + 1567854 * 2 ^ 59
def prefixEnd_1567854 : Nat := 4983230072969 + 3 ^ 40 * 1567854 * 2
def baseEnd_1567854 : Nat := 805062698074413997714577

theorem tailTrace_1567854 : CollatzResearch.WordTrace tailWord_1567854 prefixEnd_1567854 805062698074413997714577 := by
  unfold tailWord_1567854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148041657742525123774827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38122888841293467326799077 7148041657742525123774827)
  ·
    refine ⟨10722062486613787685662241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7148041657742525123774827 10722062486613787685662241)
    ·
      refine ⟨8041546864960340764246681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10722062486613787685662241 8041546864960340764246681)
      ·
        refine ⟨6031160148720255573185011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041546864960340764246681 6031160148720255573185011)
        ·
          refine ⟨9046740223080383359777517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031160148720255573185011 9046740223080383359777517)
          ·
            refine ⟨3392527583655143759916569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9046740223080383359777517 3392527583655143759916569)
            ·
              refine ⟨2544395687741357819937427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3392527583655143759916569 2544395687741357819937427)
              ·
                refine ⟨3816593531612036729906141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544395687741357819937427 3816593531612036729906141)
                ·
                  refine ⟨1431222574354513773714803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3816593531612036729906141 1431222574354513773714803)
                  ·
                    refine ⟨2146833861531770660572205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1431222574354513773714803 2146833861531770660572205)
                    ·
                      refine ⟨805062698074413997714577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2146833861531770660572205 805062698074413997714577)
                      ·
                        rfl

theorem cell23_1567854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1567854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567854 prefixEnd_1567854 := by exact prefixLift 1567854
  have htrace : WordTrace (prefixWord ++ tailWord_1567854) baseStart_1567854 baseEnd_1567854 := by
    simpa [prefixWord, tailWord_1567854, baseEnd_1567854] using wordTrace_append hprefix tailTrace_1567854
  have hstable : (prefixWord ++ tailWord_1567854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567854).length < 2 ^ (prefixWord ++ tailWord_1567854).sum := by decide
  have hdescent : baseEnd_1567854 < baseStart_1567854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567900 : List Nat := [2, 2, 3, 2, 1, 4, 9]
def baseStart_1567900 : Nat := 118140960795 + 1567900 * 2 ^ 59
def prefixEnd_1567900 : Nat := 4983230072969 + 3 ^ 40 * 1567900 * 2
def baseEnd_1567900 : Nat := 9939337261537294046165

theorem tailTrace_1567900 : CollatzResearch.WordTrace tailWord_1567900 prefixEnd_1567900 9939337261537294046165 := by
  unfold tailWord_1567900
  simp only [CollatzResearch.WordTrace]
  refine ⟨28593005509886775423186577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38124007346515700564248769 28593005509886775423186577)
  ·
    refine ⟨21444754132415081567389933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28593005509886775423186577 21444754132415081567389933)
    ·
      refine ⟨8041782799655655587771225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21444754132415081567389933 8041782799655655587771225)
      ·
        refine ⟨6031337099741741690828419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041782799655655587771225 6031337099741741690828419)
        ·
          refine ⟨9047005649612612536242629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031337099741741690828419 9047005649612612536242629)
          ·
            refine ⟨1696313559302364850545493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9047005649612612536242629 1696313559302364850545493)
            ·
              refine ⟨9939337261537294046165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1696313559302364850545493 9939337261537294046165)
              ·
                rfl

theorem cell23_1567900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 9].length) (baseStart_1567900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567900 prefixEnd_1567900 := by exact prefixLift 1567900
  have htrace : WordTrace (prefixWord ++ tailWord_1567900) baseStart_1567900 baseEnd_1567900 := by
    simpa [prefixWord, tailWord_1567900, baseEnd_1567900] using wordTrace_append hprefix tailTrace_1567900
  have hstable : (prefixWord ++ tailWord_1567900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567900).length < 2 ^ (prefixWord ++ tailWord_1567900).sum := by decide
  have hdescent : baseEnd_1567900 < baseStart_1567900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567911 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1567911 : Nat := 118140960795 + 1567911 * 2 ^ 59
def prefixEnd_1567911 : Nat := 4983230072969 + 3 ^ 40 * 1567911 * 2
def baseEnd_1567911 : Nat := 805091966471720274701815

theorem tailTrace_1567911 : CollatzResearch.WordTrace tailWord_1567911 prefixEnd_1567911 805091966471720274701815 := by
  unfold tailWord_1567911
  simp only [CollatzResearch.WordTrace]
  refine ⟨57186412222733699725023587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38124274815155799816682391 57186412222733699725023587)
  ·
    refine ⟨85779618334100549587535381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57186412222733699725023587 85779618334100549587535381)
    ·
      refine ⟨4020919609410963261915721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85779618334100549587535381 4020919609410963261915721)
      ·
        refine ⟨3015689707058222446436791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4020919609410963261915721 3015689707058222446436791)
        ·
          refine ⟨4523534560587333669655187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015689707058222446436791 4523534560587333669655187)
          ·
            refine ⟨6785301840881000504482781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523534560587333669655187 6785301840881000504482781)
            ·
              refine ⟨2544488190330375189181043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6785301840881000504482781 2544488190330375189181043)
              ·
                refine ⟨3816732285495562783771565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544488190330375189181043 3816732285495562783771565)
                ·
                  refine ⟨1431274607060836043914337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3816732285495562783771565 1431274607060836043914337)
                  ·
                    refine ⟨1073455955295627032935753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431274607060836043914337 1073455955295627032935753)
                    ·
                      refine ⟨805091966471720274701815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073455955295627032935753 805091966471720274701815)
                      ·
                        rfl

theorem cell23_1567911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1567911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567911 prefixEnd_1567911 := by exact prefixLift 1567911
  have htrace : WordTrace (prefixWord ++ tailWord_1567911) baseStart_1567911 baseEnd_1567911 := by
    simpa [prefixWord, tailWord_1567911, baseEnd_1567911] using wordTrace_append hprefix tailTrace_1567911
  have hstable : (prefixWord ++ tailWord_1567911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567911).length < 2 ^ (prefixWord ++ tailWord_1567911).sum := by decide
  have hdescent : baseEnd_1567911 < baseStart_1567911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567917 : List Nat := [1, 5, 2, 1, 3, 1, 2, 8]
def baseStart_1567917 : Nat := 118140960795 + 1567917 * 2 ^ 59
def prefixEnd_1567917 : Nat := 4983230072969 + 3 ^ 40 * 1567917 * 2
def baseEnd_1567917 : Nat := 29818335087246194489881

theorem tailTrace_1567917 : CollatzResearch.WordTrace tailWord_1567917 prefixEnd_1567917 29818335087246194489881 := by
  unfold tailWord_1567917
  simp only [CollatzResearch.WordTrace]
  refine ⟨57186631060711962749742005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38124420707141308499828003 57186631060711962749742005)
  ·
    refine ⟨5361246661941746507788313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57186631060711962749742005 5361246661941746507788313)
    ·
      refine ⟨4020934996456309880841235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5361246661941746507788313 4020934996456309880841235)
      ·
        refine ⟨6031402494684464821261853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020934996456309880841235 6031402494684464821261853)
        ·
          refine ⟨2261775935506674307973195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6031402494684464821261853 2261775935506674307973195)
          ·
            refine ⟨3392663903260011461959793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261775935506674307973195 3392663903260011461959793)
            ·
              refine ⟨2544497927445008596469845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3392663903260011461959793 2544497927445008596469845)
              ·
                refine ⟨29818335087246194489881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2544497927445008596469845 29818335087246194489881)
                ·
                  rfl

theorem cell23_1567917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 8].length) (baseStart_1567917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567917 prefixEnd_1567917 := by exact prefixLift 1567917
  have htrace : WordTrace (prefixWord ++ tailWord_1567917) baseStart_1567917 baseEnd_1567917 := by
    simpa [prefixWord, tailWord_1567917, baseEnd_1567917] using wordTrace_append hprefix tailTrace_1567917
  have hstable : (prefixWord ++ tailWord_1567917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567917).length < 2 ^ (prefixWord ++ tailWord_1567917).sum := by decide
  have hdescent : baseEnd_1567917 < baseStart_1567917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567921 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 2, 4]
def baseStart_1567921 : Nat := 118140960795 + 1567921 * 2 ^ 59
def prefixEnd_1567921 : Nat := 4983230072969 + 3 ^ 40 * 1567921 * 2
def baseEnd_1567921 : Nat := 268365700426088411858923

theorem tailTrace_1567921 : CollatzResearch.WordTrace tailWord_1567921 prefixEnd_1567921 268365700426088411858923 := by
  unfold tailWord_1567921
  simp only [CollatzResearch.WordTrace]
  refine ⟨57186776952697471432887617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38124517968464980955258411 57186776952697471432887617)
  ·
    refine ⟨42890082714523103574665713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57186776952697471432887617 42890082714523103574665713)
    ·
      refine ⟨32167562035892327680999285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42890082714523103574665713 32167562035892327680999285)
      ·
        refine ⟨3015708940864905720093683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32167562035892327680999285 3015708940864905720093683)
        ·
          refine ⟨4523563411297358580140525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015708940864905720093683 4523563411297358580140525)
          ·
            refine ⟨1696336279236509467552697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4523563411297358580140525 1696336279236509467552697)
            ·
              refine ⟨1272252209427382100664523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696336279236509467552697 1272252209427382100664523)
              ·
                refine ⟨1908378314141073150996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272252209427382100664523 1908378314141073150996785)
                ·
                  refine ⟨1431283735605804863247589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908378314141073150996785 1431283735605804863247589)
                  ·
                    refine ⟨268365700426088411858923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431283735605804863247589 268365700426088411858923)
                    ·
                      rfl

theorem cell23_1567921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_1567921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567921 prefixEnd_1567921 := by exact prefixLift 1567921
  have htrace : WordTrace (prefixWord ++ tailWord_1567921) baseStart_1567921 baseEnd_1567921 := by
    simpa [prefixWord, tailWord_1567921, baseEnd_1567921] using wordTrace_append hprefix tailTrace_1567921
  have hstable : (prefixWord ++ tailWord_1567921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567921).length < 2 ^ (prefixWord ++ tailWord_1567921).sum := by decide
  have hdescent : baseEnd_1567921 < baseStart_1567921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567980 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1567980 : Nat := 118140960795 + 1567980 * 2 ^ 59
def prefixEnd_1567980 : Nat := 4983230072969 + 3 ^ 40 * 1567980 * 2
def baseEnd_1567980 : Nat := 805127396636880504738997

theorem tailTrace_1567980 : CollatzResearch.WordTrace tailWord_1567980 prefixEnd_1567980 805127396636880504738997 := by
  unfold tailWord_1567980
  simp only [CollatzResearch.WordTrace]
  refine ⟨28594464429741862254642697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38125952572989149672856929 28594464429741862254642697)
  ·
    refine ⟨21445848322306396690982023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28594464429741862254642697 21445848322306396690982023)
    ·
      refine ⟨32168772483459595036473035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21445848322306396690982023 32168772483459595036473035)
      ·
        refine ⟨48253158725189392554709553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32168772483459595036473035 48253158725189392554709553)
        ·
          refine ⟨36189869043892044416032165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48253158725189392554709553 36189869043892044416032165)
          ·
            refine ⟨6785600445729758328006031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36189869043892044416032165 6785600445729758328006031)
            ·
              refine ⟨10178400668594637492009047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785600445729758328006031 10178400668594637492009047)
              ·
                refine ⟨15267601002891956238013571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10178400668594637492009047 15267601002891956238013571)
                ·
                  refine ⟨22901401504337934357020357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15267601002891956238013571 22901401504337934357020357)
                  ·
                    refine ⟨4294012782063362691941317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22901401504337934357020357 4294012782063362691941317)
                    ·
                      refine ⟨805127396636880504738997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4294012782063362691941317 805127396636880504738997)
                      ·
                        rfl

theorem cell23_1567980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1567980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1567980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1567980 prefixEnd_1567980 := by exact prefixLift 1567980
  have htrace : WordTrace (prefixWord ++ tailWord_1567980) baseStart_1567980 baseEnd_1567980 := by
    simpa [prefixWord, tailWord_1567980, baseEnd_1567980] using wordTrace_append hprefix tailTrace_1567980
  have hstable : (prefixWord ++ tailWord_1567980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567980).length < 2 ^ (prefixWord ++ tailWord_1567980).sum := by decide
  have hdescent : baseEnd_1567980 < baseStart_1567980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568000 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_1568000 : Nat := 118140960795 + 1568000 * 2 ^ 59
def prefixEnd_1568000 : Nat := 4983230072969 + 3 ^ 40 * 1568000 * 2
def baseEnd_1568000 : Nat := 805137666249970426488905

theorem tailTrace_1568000 : CollatzResearch.WordTrace tailWord_1568000 prefixEnd_1568000 805137666249970426488905 := by
  unfold tailWord_1568000
  simp only [CollatzResearch.WordTrace]
  refine ⟨28594829159705633962506727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38126438879607511950008969 28594829159705633962506727)
  ·
    refine ⟨42892243739558450943760091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28594829159705633962506727 42892243739558450943760091)
    ·
      refine ⟨64338365609337676415640137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42892243739558450943760091 64338365609337676415640137)
      ·
        refine ⟨48253774207003257311730103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64338365609337676415640137 48253774207003257311730103)
        ·
          refine ⟨72380661310504885967595155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48253774207003257311730103 72380661310504885967595155)
          ·
            refine ⟨108570991965757328951392733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72380661310504885967595155 108570991965757328951392733)
            ·
              refine ⟨40714121987158998356772275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108570991965757328951392733 40714121987158998356772275)
              ·
                refine ⟨61071182980738497535158413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40714121987158998356772275 61071182980738497535158413)
                ·
                  refine ⟨22901693617776936575684405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61071182980738497535158413 22901693617776936575684405)
                  ·
                    refine ⟨2147033776666587803970413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22901693617776936575684405 2147033776666587803970413)
                    ·
                      refine ⟨805137666249970426488905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147033776666587803970413 805137666249970426488905)
                      ·
                        rfl

theorem cell23_1568000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_1568000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568000 prefixEnd_1568000 := by exact prefixLift 1568000
  have htrace : WordTrace (prefixWord ++ tailWord_1568000) baseStart_1568000 baseEnd_1568000 := by
    simpa [prefixWord, tailWord_1568000, baseEnd_1568000] using wordTrace_append hprefix tailTrace_1568000
  have hstable : (prefixWord ++ tailWord_1568000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568000).length < 2 ^ (prefixWord ++ tailWord_1568000).sum := by decide
  have hdescent : baseEnd_1568000 < baseStart_1568000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568080 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 8]
def baseStart_1568080 : Nat := 118140960795 + 1568080 * 2 ^ 59
def prefixEnd_1568080 : Nat := 4983230072969 + 3 ^ 40 * 1568080 * 2
def baseEnd_1568080 : Nat := 89464304966925568165393

theorem tailTrace_1568080 : CollatzResearch.WordTrace tailWord_1568080 prefixEnd_1568080 89464304966925568165393 := by
  unfold tailWord_1568080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28596288079560720793962847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38128384106080961058617129 28596288079560720793962847)
  ·
    refine ⟨42894432119341081190944271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28596288079560720793962847 42894432119341081190944271)
    ·
      refine ⟨64341648179011621786416407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42894432119341081190944271 64341648179011621786416407)
      ·
        refine ⟨96512472268517432679624611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64341648179011621786416407 96512472268517432679624611)
        ·
          refine ⟨144768708402776149019436917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96512472268517432679624611 144768708402776149019436917)
          ·
            refine ⟨13572066412760263970572211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144768708402776149019436917 13572066412760263970572211)
            ·
              refine ⟨20358099619140395955858317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13572066412760263970572211 20358099619140395955858317)
              ·
                refine ⟨7634287357177648483446869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20358099619140395955858317 7634287357177648483446869)
                ·
                  refine ⟨89464304966925568165393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7634287357177648483446869 89464304966925568165393)
                  ·
                    rfl

theorem cell23_1568080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_1568080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568080 prefixEnd_1568080 := by exact prefixLift 1568080
  have htrace : WordTrace (prefixWord ++ tailWord_1568080) baseStart_1568080 baseEnd_1568080 := by
    simpa [prefixWord, tailWord_1568080, baseEnd_1568080] using wordTrace_append hprefix tailTrace_1568080
  have hstable : (prefixWord ++ tailWord_1568080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568080).length < 2 ^ (prefixWord ++ tailWord_1568080).sum := by decide
  have hdescent : baseEnd_1568080 < baseStart_1568080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
