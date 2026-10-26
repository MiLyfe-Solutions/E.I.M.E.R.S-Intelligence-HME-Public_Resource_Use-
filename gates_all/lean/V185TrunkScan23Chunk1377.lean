import V185TrunkScan23Chunk1376

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8155909 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_8155909 : Nat := 118140960795 + 8155909 * 2 ^ 59
def prefixEnd_8155909 : Nat := 4983230072969 + 3 ^ 40 * 8155909 * 2
def baseEnd_8155909 : Nat := 1395967163776878567409721

theorem tailTrace_8155909 : CollatzResearch.WordTrace tailWord_8155909 prefixEnd_8155909 1395967163776878567409721 := by
  unfold tailWord_8155909
  simp only [CollatzResearch.WordTrace]
  refine ⟨297470439409542086206414781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198313626273028057470943187 297470439409542086206414781)
  ·
    refine ⟨111551414778578282327405543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297470439409542086206414781 111551414778578282327405543)
    ·
      refine ⟨167327122167867423491108315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111551414778578282327405543 167327122167867423491108315)
      ·
        refine ⟨250990683251801135236662473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167327122167867423491108315 250990683251801135236662473)
        ·
          refine ⟨188243012438850851427496855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250990683251801135236662473 188243012438850851427496855)
          ·
            refine ⟨282364518658276277141245283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188243012438850851427496855 282364518658276277141245283)
            ·
              refine ⟨423546777987414415711867925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282364518658276277141245283 423546777987414415711867925)
              ·
                refine ⟨19853755218160050736493809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 423546777987414415711867925 19853755218160050736493809)
                ·
                  refine ⟨14890316413620038052370357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19853755218160050736493809 14890316413620038052370357)
                  ·
                    refine ⟨1395967163776878567409721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14890316413620038052370357 1395967163776878567409721)
                    ·
                      rfl

theorem cell23_8155909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_8155909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155909 prefixEnd_8155909 := by exact prefixLift 8155909
  have htrace : WordTrace (prefixWord ++ tailWord_8155909) baseStart_8155909 baseEnd_8155909 := by
    simpa [prefixWord, tailWord_8155909, baseEnd_8155909] using wordTrace_append hprefix tailTrace_8155909
  have hstable : (prefixWord ++ tailWord_8155909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155909).length < 2 ^ (prefixWord ++ tailWord_8155909).sum := by decide
  have hdescent : baseEnd_8155909 < baseStart_8155909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155929 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_8155929 : Nat := 118140960795 + 8155929 * 2 ^ 59
def prefixEnd_8155929 : Nat := 4983230072969 + 3 ^ 40 * 8155929 * 2
def baseEnd_8155929 : Nat := 4187911760943725623979071

theorem tailTrace_8155929 : CollatzResearch.WordTrace tailWord_8155929 prefixEnd_8155929 4187911760943725623979071 := by
  unfold tailWord_8155929
  simp only [CollatzResearch.WordTrace]
  refine ⟨297471168869469629622142841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198314112579646419748095227 297471168869469629622142841)
  ·
    refine ⟨223103376652102222216607131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297471168869469629622142841 223103376652102222216607131)
    ·
      refine ⟨334655064978153333324910697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223103376652102222216607131 334655064978153333324910697)
      ·
        refine ⟨250991298733614999993683023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334655064978153333324910697 250991298733614999993683023)
        ·
          refine ⟨376486948100422499990524535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250991298733614999993683023 376486948100422499990524535)
          ·
            refine ⟨564730422150633749985786803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376486948100422499990524535 564730422150633749985786803)
            ·
              refine ⟨847095633225950624978680205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564730422150633749985786803 847095633225950624978680205)
              ·
                refine ⟨317660862459731484367005077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847095633225950624978680205 317660862459731484367005077)
                ·
                  refine ⟨14890352927799913329703363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317660862459731484367005077 14890352927799913329703363)
                  ·
                    refine ⟨22335529391699869994555045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14890352927799913329703363 22335529391699869994555045)
                    ·
                      refine ⟨4187911760943725623979071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22335529391699869994555045 4187911760943725623979071)
                      ·
                        rfl

theorem cell23_8155929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_8155929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155929 prefixEnd_8155929 := by exact prefixLift 8155929
  have htrace : WordTrace (prefixWord ++ tailWord_8155929) baseStart_8155929 baseEnd_8155929 := by
    simpa [prefixWord, tailWord_8155929, baseEnd_8155929] using wordTrace_append hprefix tailTrace_8155929
  have hstable : (prefixWord ++ tailWord_8155929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155929).length < 2 ^ (prefixWord ++ tailWord_8155929).sum := by decide
  have hdescent : baseEnd_8155929 < baseStart_8155929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155986 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_8155986 : Nat := 118140960795 + 8155986 * 2 ^ 59
def prefixEnd_8155986 : Nat := 4983230072969 + 3 ^ 40 * 8155986 * 2
def baseEnd_8155986 : Nat := 465326781037892433440701

theorem tailTrace_8155986 : CollatzResearch.WordTrace tailWord_8155986 prefixEnd_8155986 465326781037892433440701 := by
  unfold tailWord_8155986
  simp only [CollatzResearch.WordTrace]
  refine ⟨74368311957565782089241953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198315498553508752237978541 74368311957565782089241953)
  ·
    refine ⟨55776233968174336566931465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74368311957565782089241953 55776233968174336566931465)
    ·
      refine ⟨41832175476130752425198599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55776233968174336566931465 41832175476130752425198599)
      ·
        refine ⟨62748263214196128637797899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41832175476130752425198599 62748263214196128637797899)
        ·
          refine ⟨94122394821294192956696849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62748263214196128637797899 94122394821294192956696849)
          ·
            refine ⟨70591796115970644717522637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94122394821294192956696849 70591796115970644717522637)
            ·
              refine ⟨26471923543488991769070989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70591796115970644717522637 26471923543488991769070989)
              ·
                refine ⟨9926971328808371913401621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26471923543488991769070989 9926971328808371913401621)
                ·
                  refine ⟨465326781037892433440701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9926971328808371913401621 465326781037892433440701)
                  ·
                    rfl

theorem cell23_8155986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_8155986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155986 prefixEnd_8155986 := by exact prefixLift 8155986
  have htrace : WordTrace (prefixWord ++ tailWord_8155986) baseStart_8155986 baseEnd_8155986 := by
    simpa [prefixWord, tailWord_8155986, baseEnd_8155986] using wordTrace_append hprefix tailTrace_8155986
  have hstable : (prefixWord ++ tailWord_8155986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155986).length < 2 ^ (prefixWord ++ tailWord_8155986).sum := by decide
  have hdescent : baseEnd_8155986 < baseStart_8155986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156016 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 1, 5]
def baseStart_8156016 : Nat := 118140960795 + 8156016 * 2 ^ 59
def prefixEnd_8156016 : Nat := 4983230072969 + 3 ^ 40 * 8156016 * 2
def baseEnd_8156016 : Nat := 1395985477920222261197057

theorem tailTrace_8156016 : CollatzResearch.WordTrace tailWord_8156016 prefixEnd_8156016 1395985477920222261197057 := by
  unfold tailWord_8156016
  simp only [CollatzResearch.WordTrace]
  refine ⟨148737171010077221740279951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198316228013436295653706601 148737171010077221740279951)
  ·
    refine ⟨223105756515115832610419927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148737171010077221740279951 223105756515115832610419927)
    ·
      refine ⟨334658634772673748915629891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223105756515115832610419927 334658634772673748915629891)
      ·
        refine ⟨501987952159010623373444837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334658634772673748915629891 501987952159010623373444837)
        ·
          refine ⟨94122741029814491882520907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501987952159010623373444837 94122741029814491882520907)
          ·
            refine ⟨141184111544721737823781361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94122741029814491882520907 141184111544721737823781361)
            ·
              refine ⟨105888083658541303367836021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141184111544721737823781361 105888083658541303367836021)
              ·
                refine ⟨9927007842988247190734627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105888083658541303367836021 9927007842988247190734627)
                ·
                  refine ⟨14890511764482370786101941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9927007842988247190734627 14890511764482370786101941)
                  ·
                    refine ⟨1395985477920222261197057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14890511764482370786101941 1395985477920222261197057)
                    ·
                      rfl

theorem cell23_8156016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_8156016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156016 prefixEnd_8156016 := by exact prefixLift 8156016
  have htrace : WordTrace (prefixWord ++ tailWord_8156016) baseStart_8156016 baseEnd_8156016 := by
    simpa [prefixWord, tailWord_8156016, baseEnd_8156016] using wordTrace_append hprefix tailTrace_8156016
  have hstable : (prefixWord ++ tailWord_8156016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156016).length < 2 ^ (prefixWord ++ tailWord_8156016).sum := by decide
  have hdescent : baseEnd_8156016 < baseStart_8156016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156073 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 3]
def baseStart_8156073 : Nat := 118140960795 + 8156073 * 2 ^ 59
def prefixEnd_8156073 : Nat := 4983230072969 + 3 ^ 40 * 8156073 * 2
def baseEnd_8156073 : Nat := 4187985702157973060578409

theorem tailTrace_8156073 : CollatzResearch.WordTrace tailWord_8156073 prefixEnd_8156073 4187985702157973060578409 := by
  unfold tailWord_8156073
  simp only [CollatzResearch.WordTrace]
  refine ⟨297476420980947942215384873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198317613987298628143589915 297476420980947942215384873)
  ·
    refine ⟨223107315735710956661538655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297476420980947942215384873 223107315735710956661538655)
    ·
      refine ⟨334660973603566434992307983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223107315735710956661538655 334660973603566434992307983)
      ·
        refine ⟨501991460405349652488461975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334660973603566434992307983 501991460405349652488461975)
        ·
          refine ⟨752987190608024478732692963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501991460405349652488461975 752987190608024478732692963)
          ·
            refine ⟨1129480785912036718099039445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752987190608024478732692963 1129480785912036718099039445)
            ·
              refine ⟨26472205919813360580446237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1129480785912036718099039445 26472205919813360580446237)
              ·
                refine ⟨9927077219930010217667339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26472205919813360580446237 9927077219930010217667339)
                ·
                  refine ⟨14890615829895015326501009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9927077219930010217667339 14890615829895015326501009)
                  ·
                    refine ⟨11167961872421261494875757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14890615829895015326501009 11167961872421261494875757)
                    ·
                      refine ⟨4187985702157973060578409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11167961872421261494875757 4187985702157973060578409)
                      ·
                        rfl

theorem cell23_8156073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_8156073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156073 prefixEnd_8156073 := by exact prefixLift 8156073
  have htrace : WordTrace (prefixWord ++ tailWord_8156073) baseStart_8156073 baseEnd_8156073 := by
    simpa [prefixWord, tailWord_8156073, baseEnd_8156073] using wordTrace_append hprefix tailTrace_8156073
  have hstable : (prefixWord ++ tailWord_8156073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156073).length < 2 ^ (prefixWord ++ tailWord_8156073).sum := by decide
  have hdescent : baseEnd_8156073 < baseStart_8156073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156087 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 1, 2, 2]
def baseStart_8156087 : Nat := 118140960795 + 8156087 * 2 ^ 59
def prefixEnd_8156087 : Nat := 4983230072969 + 3 ^ 40 * 8156087 * 2
def baseEnd_8156087 : Nat := 4187992890887136005803345

theorem tailTrace_8156087 : CollatzResearch.WordTrace tailWord_8156087 prefixEnd_8156087 4187992890887136005803345 := by
  unfold tailWord_8156087
  simp only [CollatzResearch.WordTrace]
  refine ⟨297476931602897222606394515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198317954401931481737596343 297476931602897222606394515)
  ·
    refine ⟨446215397404345833909591773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297476931602897222606394515 446215397404345833909591773)
    ·
      refine ⟨167330774026629687716096915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446215397404345833909591773 167330774026629687716096915)
      ·
        refine ⟨250996161039944531574145373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167330774026629687716096915 250996161039944531574145373)
        ·
          refine ⟨94123560389979199340304515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250996161039944531574145373 94123560389979199340304515)
          ·
            refine ⟨141185340584968799010456773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94123560389979199340304515 141185340584968799010456773)
            ·
              refine ⟨26472251359681649814460645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141185340584968799010456773 26472251359681649814460645)
              ·
                refine ⟨4963547129940309340211371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26472251359681649814460645 4963547129940309340211371)
                ·
                  refine ⟨7445320694910464010317057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963547129940309340211371 7445320694910464010317057)
                  ·
                    refine ⟨5583990521182848007737793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445320694910464010317057 5583990521182848007737793)
                    ·
                      refine ⟨4187992890887136005803345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583990521182848007737793 4187992890887136005803345)
                      ·
                        rfl

theorem cell23_8156087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_8156087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156087 prefixEnd_8156087 := by exact prefixLift 8156087
  have htrace : WordTrace (prefixWord ++ tailWord_8156087) baseStart_8156087 baseEnd_8156087 := by
    simpa [prefixWord, tailWord_8156087, baseEnd_8156087] using wordTrace_append hprefix tailTrace_8156087
  have hstable : (prefixWord ++ tailWord_8156087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156087).length < 2 ^ (prefixWord ++ tailWord_8156087).sum := by decide
  have hdescent : baseEnd_8156087 < baseStart_8156087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156100 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_8156100 : Nat := 118140960795 + 8156100 * 2 ^ 59
def prefixEnd_8156100 : Nat := 4983230072969 + 3 ^ 40 * 8156100 * 2
def baseEnd_8156100 : Nat := 4187999566135644454940785

theorem tailTrace_8156100 : CollatzResearch.WordTrace tailWord_8156100 prefixEnd_8156100 4187999566135644454940785 := by
  unfold tailWord_8156100
  simp only [CollatzResearch.WordTrace]
  refine ⟨148738702875925062913308877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198318270501233417217745169 148738702875925062913308877)
  ·
    refine ⟨55777013578471898592490829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148738702875925062913308877 55777013578471898592490829)
    ·
      refine ⟨20916380091926961972184061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55777013578471898592490829 20916380091926961972184061)
      ·
        refine ⟨7843642534472610739569023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20916380091926961972184061 7843642534472610739569023)
        ·
          refine ⟨11765463801708916109353535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7843642534472610739569023 11765463801708916109353535)
          ·
            refine ⟨17648195702563374164030303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765463801708916109353535 17648195702563374164030303)
            ·
              refine ⟨26472293553845061246045455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17648195702563374164030303 26472293553845061246045455)
              ·
                refine ⟨39708440330767591869068183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26472293553845061246045455 39708440330767591869068183)
                ·
                  refine ⟨59562660496151387803602275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39708440330767591869068183 59562660496151387803602275)
                  ·
                    refine ⟨89343990744227081705403413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59562660496151387803602275 89343990744227081705403413)
                    ·
                      refine ⟨4187999566135644454940785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89343990744227081705403413 4187999566135644454940785)
                      ·
                        rfl

theorem cell23_8156100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_8156100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156100 prefixEnd_8156100 := by exact prefixLift 8156100
  have htrace : WordTrace (prefixWord ++ tailWord_8156100) baseStart_8156100 baseEnd_8156100 := by
    simpa [prefixWord, tailWord_8156100, baseEnd_8156100] using wordTrace_append hprefix tailTrace_8156100
  have hstable : (prefixWord ++ tailWord_8156100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156100).length < 2 ^ (prefixWord ++ tailWord_8156100).sum := by decide
  have hdescent : baseEnd_8156100 < baseStart_8156100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156103 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_8156103 : Nat := 118140960795 + 8156103 * 2 ^ 59
def prefixEnd_8156103 : Nat := 4983230072969 + 3 ^ 40 * 8156103 * 2
def baseEnd_8156103 : Nat := 4188001106577607943203271

theorem tailTrace_8156103 : CollatzResearch.WordTrace tailWord_8156103 prefixEnd_8156103 4188001106577607943203271 := by
  unfold tailWord_8156103
  simp only [CollatzResearch.WordTrace]
  refine ⟨297477515170839257338976963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198318343447226171559317975 297477515170839257338976963)
  ·
    refine ⟨446216272756258886008465445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297477515170839257338976963 446216272756258886008465445)
    ·
      refine ⟨83665551141798541126587271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446216272756258886008465445 83665551141798541126587271)
      ·
        refine ⟨125498326712697811689880907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83665551141798541126587271 125498326712697811689880907)
        ·
          refine ⟨188247490069046717534821361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125498326712697811689880907 188247490069046717534821361)
          ·
            refine ⟨141185617551785038151116021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188247490069046717534821361 141185617551785038151116021)
            ·
              refine ⟨13236151645479847326667127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141185617551785038151116021 13236151645479847326667127)
              ·
                refine ⟨19854227468219770990000691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13236151645479847326667127 19854227468219770990000691)
                ·
                  refine ⟨29781341202329656485001037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19854227468219770990000691 29781341202329656485001037)
                  ·
                    refine ⟨11168002950873621181875389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29781341202329656485001037 11168002950873621181875389)
                    ·
                      refine ⟨4188001106577607943203271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11168002950873621181875389 4188001106577607943203271)
                      ·
                        rfl

theorem cell23_8156103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_8156103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156103 prefixEnd_8156103 := by exact prefixLift 8156103
  have htrace : WordTrace (prefixWord ++ tailWord_8156103) baseStart_8156103 baseEnd_8156103 := by
    simpa [prefixWord, tailWord_8156103, baseEnd_8156103] using wordTrace_append hprefix tailTrace_8156103
  have hstable : (prefixWord ++ tailWord_8156103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156103).length < 2 ^ (prefixWord ++ tailWord_8156103).sum := by decide
  have hdescent : baseEnd_8156103 < baseStart_8156103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156136 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_8156136 : Nat := 118140960795 + 8156136 * 2 ^ 59
def prefixEnd_8156136 : Nat := 4983230072969 + 3 ^ 40 * 8156136 * 2
def baseEnd_8156136 : Nat := 1396006017146402104696873

theorem tailTrace_8156136 : CollatzResearch.WordTrace tailWord_8156136 prefixEnd_8156136 1396006017146402104696873 := by
  unfold tailWord_8156136
  simp only [CollatzResearch.WordTrace]
  refine ⟨148739359389859851987464131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198319145853146469316618841 148739359389859851987464131)
  ·
    refine ⟨223109039084789777981196197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148739359389859851987464131 223109039084789777981196197)
    ·
      refine ⟨41832944828398083371474287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223109039084789777981196197 41832944828398083371474287)
      ·
        refine ⟨62749417242597125057211431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41832944828398083371474287 62749417242597125057211431)
        ·
          refine ⟨94124125863895687585817147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62749417242597125057211431 94124125863895687585817147)
          ·
            refine ⟨141186188795843531378725721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94124125863895687585817147 141186188795843531378725721)
            ·
              refine ⟨105889641596882648534044291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141186188795843531378725721 105889641596882648534044291)
              ·
                refine ⟨158834462395323972801066437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105889641596882648534044291 158834462395323972801066437)
                ·
                  refine ⟨29781461699123244900199957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158834462395323972801066437 29781461699123244900199957)
                  ·
                    refine ⟨1396006017146402104696873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29781461699123244900199957 1396006017146402104696873)
                    ·
                      rfl

theorem cell23_8156136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_8156136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156136 prefixEnd_8156136 := by exact prefixLift 8156136
  have htrace : WordTrace (prefixWord ++ tailWord_8156136) baseStart_8156136 baseEnd_8156136 := by
    simpa [prefixWord, tailWord_8156136, baseEnd_8156136] using wordTrace_append hprefix tailTrace_8156136
  have hstable : (prefixWord ++ tailWord_8156136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156136).length < 2 ^ (prefixWord ++ tailWord_8156136).sum := by decide
  have hdescent : baseEnd_8156136 < baseStart_8156136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156194 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_8156194 : Nat := 118140960795 + 8156194 * 2 ^ 59
def prefixEnd_8156194 : Nat := 4983230072969 + 3 ^ 40 * 8156194 * 2
def baseEnd_8156194 : Nat := 4188047833317167087165353

theorem tailTrace_8156194 : CollatzResearch.WordTrace tailWord_8156194 prefixEnd_8156194 4188047833317167087165353 := by
  unfold tailWord_8156194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74370208553377394970134909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198320556142339719920359757 74370208553377394970134909)
  ·
    refine ⟨27888828207516523113800591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74370208553377394970134909 27888828207516523113800591)
    ·
      refine ⟨41833242311274784670700887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27888828207516523113800591 41833242311274784670700887)
      ·
        refine ⟨62749863466912177006051331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41833242311274784670700887 62749863466912177006051331)
        ·
          refine ⟨94124795200368265509076997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62749863466912177006051331 94124795200368265509076997)
          ·
            refine ⟨17648399100069049782951937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94124795200368265509076997 17648399100069049782951937)
            ·
              refine ⟨13236299325051787337213953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17648399100069049782951937 13236299325051787337213953)
              ·
                refine ⟨9927224493788840502910465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13236299325051787337213953 9927224493788840502910465)
                ·
                  refine ⟨7445418370341630377182849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9927224493788840502910465 7445418370341630377182849)
                  ·
                    refine ⟨5584063777756222782887137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445418370341630377182849 5584063777756222782887137)
                    ·
                      refine ⟨4188047833317167087165353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584063777756222782887137 4188047833317167087165353)
                      ·
                        rfl

theorem cell23_8156194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_8156194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156194 prefixEnd_8156194 := by exact prefixLift 8156194
  have htrace : WordTrace (prefixWord ++ tailWord_8156194) baseStart_8156194 baseEnd_8156194 := by
    simpa [prefixWord, tailWord_8156194, baseEnd_8156194] using wordTrace_append hprefix tailTrace_8156194
  have hstable : (prefixWord ++ tailWord_8156194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156194).length < 2 ^ (prefixWord ++ tailWord_8156194).sum := by decide
  have hdescent : baseEnd_8156194 < baseStart_8156194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156203 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 7, 2]
def baseStart_8156203 : Nat := 118140960795 + 8156203 * 2 ^ 59
def prefixEnd_8156203 : Nat := 4983230072969 + 3 ^ 40 * 8156203 * 2
def baseEnd_8156203 : Nat := 4188052454643057551952811

theorem tailTrace_8156203 : CollatzResearch.WordTrace tailWord_8156203 prefixEnd_8156203 4188052454643057551952811 := by
  unfold tailWord_8156203
  simp only [CollatzResearch.WordTrace]
  refine ⟨297481162470476974417617263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198320774980317982945078175 297481162470476974417617263)
  ·
    refine ⟨446221743705715461626425895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297481162470476974417617263 446221743705715461626425895)
    ·
      refine ⟨669332615558573192439638843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446221743705715461626425895 669332615558573192439638843)
      ·
        refine ⟨1003998923337859788659458265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669332615558573192439638843 1003998923337859788659458265)
        ·
          refine ⟨752999192503394841494593699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003998923337859788659458265 752999192503394841494593699)
          ·
            refine ⟨1129498788755092262241890549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752999192503394841494593699 1129498788755092262241890549)
            ·
              refine ⟨105890511445789899585177239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1129498788755092262241890549 105890511445789899585177239)
              ·
                refine ⟨158835767168684849377765859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105890511445789899585177239 158835767168684849377765859)
                ·
                  refine ⟨238253650753027274066648789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158835767168684849377765859 238253650753027274066648789)
                  ·
                    refine ⟨5584069939524076735937081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 238253650753027274066648789 5584069939524076735937081)
                    ·
                      refine ⟨4188052454643057551952811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584069939524076735937081 4188052454643057551952811)
                      ·
                        rfl

theorem cell23_8156203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7, 2].length) (baseStart_8156203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156203 prefixEnd_8156203 := by exact prefixLift 8156203
  have htrace : WordTrace (prefixWord ++ tailWord_8156203) baseStart_8156203 baseEnd_8156203 := by
    simpa [prefixWord, tailWord_8156203, baseEnd_8156203] using wordTrace_append hprefix tailTrace_8156203
  have hstable : (prefixWord ++ tailWord_8156203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156203).length < 2 ^ (prefixWord ++ tailWord_8156203).sum := by decide
  have hdescent : baseEnd_8156203 < baseStart_8156203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156233 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_8156233 : Nat := 118140960795 + 8156233 * 2 ^ 59
def prefixEnd_8156233 : Nat := 4983230072969 + 3 ^ 40 * 8156233 * 2
def baseEnd_8156233 : Nat := 4188067859062692434577673

theorem tailTrace_8156233 : CollatzResearch.WordTrace tailWord_8156233 prefixEnd_8156233 4188067859062692434577673 := by
  unfold tailWord_8156233
  simp only [CollatzResearch.WordTrace]
  refine ⟨297482256660368289541209353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198321504440245526360806235 297482256660368289541209353)
  ·
    refine ⟨223111692495276217155907015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297482256660368289541209353 223111692495276217155907015)
    ·
      refine ⟨334667538742914325733860523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223111692495276217155907015 334667538742914325733860523)
      ·
        refine ⟨502001308114371488600790785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334667538742914325733860523 502001308114371488600790785)
        ·
          refine ⟨376500981085778616450593089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502001308114371488600790785 376500981085778616450593089)
          ·
            refine ⟨282375735814333962337944817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376500981085778616450593089 282375735814333962337944817)
            ·
              refine ⟨211781801860750471753458613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282375735814333962337944817 211781801860750471753458613)
              ·
                refine ⟨19854543924445356726886745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211781801860750471753458613 19854543924445356726886745)
                ·
                  refine ⟨14890907943334017545165059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19854543924445356726886745 14890907943334017545165059)
                  ·
                    refine ⟨22336361915001026317747589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14890907943334017545165059 22336361915001026317747589)
                    ·
                      refine ⟨4188067859062692434577673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22336361915001026317747589 4188067859062692434577673)
                      ·
                        rfl

theorem cell23_8156233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_8156233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156233 prefixEnd_8156233 := by exact prefixLift 8156233
  have htrace : WordTrace (prefixWord ++ tailWord_8156233) baseStart_8156233 baseEnd_8156233 := by
    simpa [prefixWord, tailWord_8156233, baseEnd_8156233] using wordTrace_append hprefix tailTrace_8156233
  have hstable : (prefixWord ++ tailWord_8156233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156233).length < 2 ^ (prefixWord ++ tailWord_8156233).sum := by decide
  have hdescent : baseEnd_8156233 < baseStart_8156233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156270 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_8156270 : Nat := 118140960795 + 8156270 * 2 ^ 59
def prefixEnd_8156270 : Nat := 4983230072969 + 3 ^ 40 * 8156270 * 2
def baseEnd_8156270 : Nat := 4188086857846908789815003

theorem tailTrace_8156270 : CollatzResearch.WordTrace tailWord_8156270 prefixEnd_8156270 4188086857846908789815003 := by
  unfold tailWord_8156270
  simp only [CollatzResearch.WordTrace]
  refine ⟨37185450770154280607538283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198322404107489496573537509 37185450770154280607538283)
  ·
    refine ⟨55778176155231420911307425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37185450770154280607538283 55778176155231420911307425)
    ·
      refine ⟨41833632116423565683480569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55778176155231420911307425 41833632116423565683480569)
      ·
        refine ⟨31375224087317674262610427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41833632116423565683480569 31375224087317674262610427)
        ·
          refine ⟨47062836130976511393915641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31375224087317674262610427 47062836130976511393915641)
          ·
            refine ⟨35297127098232383545436731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47062836130976511393915641 35297127098232383545436731)
            ·
              refine ⟨52945690647348575318155097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35297127098232383545436731 52945690647348575318155097)
              ·
                refine ⟨39709267985511431488616323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52945690647348575318155097 39709267985511431488616323)
                ·
                  refine ⟨59563901978267147232924485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39709267985511431488616323 59563901978267147232924485)
                  ·
                    refine ⟨11168231620925090106173341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59563901978267147232924485 11168231620925090106173341)
                    ·
                      refine ⟨4188086857846908789815003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11168231620925090106173341 4188086857846908789815003)
                      ·
                        rfl

theorem cell23_8156270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_8156270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156270 prefixEnd_8156270 := by exact prefixLift 8156270
  have htrace : WordTrace (prefixWord ++ tailWord_8156270) baseStart_8156270 baseEnd_8156270 := by
    simpa [prefixWord, tailWord_8156270, baseEnd_8156270] using wordTrace_append hprefix tailTrace_8156270
  have hstable : (prefixWord ++ tailWord_8156270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156270).length < 2 ^ (prefixWord ++ tailWord_8156270).sum := by decide
  have hdescent : baseEnd_8156270 < baseStart_8156270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156300 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_8156300 : Nat := 118140960795 + 8156300 * 2 ^ 59
def prefixEnd_8156300 : Nat := 4983230072969 + 3 ^ 40 * 8156300 * 2
def baseEnd_8156300 : Nat := 4188102262266543672439865

theorem tailTrace_8156300 : CollatzResearch.WordTrace tailWord_8156300 prefixEnd_8156300 4188102262266543672439865 := by
  unfold tailWord_8156300
  simp only [CollatzResearch.WordTrace]
  refine ⟨148742350175562779991949177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198323133567417039989265569 148742350175562779991949177)
  ·
    refine ⟨111556762631672084993961883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148742350175562779991949177 111556762631672084993961883)
    ·
      refine ⟨167335143947508127490942825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111556762631672084993961883 167335143947508127490942825)
      ·
        refine ⟨125501357960631095618207119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167335143947508127490942825 125501357960631095618207119)
        ·
          refine ⟨188252036940946643427310679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125501357960631095618207119 188252036940946643427310679)
          ·
            refine ⟨282378055411419965140966019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188252036940946643427310679 282378055411419965140966019)
            ·
              refine ⟨423567083117129947711449029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282378055411419965140966019 423567083117129947711449029)
              ·
                refine ⟨79418828084461865195896693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423567083117129947711449029 79418828084461865195896693)
                ·
                  refine ⟨7445515132918299862115315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79418828084461865195896693 7445515132918299862115315)
                  ·
                    refine ⟨11168272699377449793172973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7445515132918299862115315 11168272699377449793172973)
                    ·
                      refine ⟨4188102262266543672439865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11168272699377449793172973 4188102262266543672439865)
                      ·
                        rfl

theorem cell23_8156300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_8156300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156300 prefixEnd_8156300 := by exact prefixLift 8156300
  have htrace : WordTrace (prefixWord ++ tailWord_8156300) baseStart_8156300 baseEnd_8156300 := by
    simpa [prefixWord, tailWord_8156300, baseEnd_8156300] using wordTrace_append hprefix tailTrace_8156300
  have hstable : (prefixWord ++ tailWord_8156300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156300).length < 2 ^ (prefixWord ++ tailWord_8156300).sum := by decide
  have hdescent : baseEnd_8156300 < baseStart_8156300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156337 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 1, 5]
def baseStart_8156337 : Nat := 118140960795 + 8156337 * 2 ^ 59
def prefixEnd_8156337 : Nat := 4983230072969 + 3 ^ 40 * 8156337 * 2
def baseEnd_8156337 : Nat := 1396040420350253342559065

theorem tailTrace_8156337 : CollatzResearch.WordTrace tailWord_8156337 prefixEnd_8156337 1396040420350253342559065 := by
  unfold tailWord_8156337
  simp only [CollatzResearch.WordTrace]
  refine ⟨297486049851991515302995265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198324033234661010201996843 297486049851991515302995265)
  ·
    refine ⟨223114537388993636477246449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297486049851991515302995265 223114537388993636477246449)
    ·
      refine ⟨167335903041745227357934837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223114537388993636477246449 167335903041745227357934837)
      ·
        refine ⟨15687740910163615064806391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167335903041745227357934837 15687740910163615064806391)
        ·
          refine ⟨23531611365245422597209587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15687740910163615064806391 23531611365245422597209587)
          ·
            refine ⟨35297417047868133895814381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23531611365245422597209587 35297417047868133895814381)
            ·
              refine ⟨13236531392950550210930393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35297417047868133895814381 13236531392950550210930393)
              ·
                refine ⟨9927398544712912658197795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13236531392950550210930393 9927398544712912658197795)
                ·
                  refine ⟨14891097817069368987296693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9927398544712912658197795 14891097817069368987296693)
                  ·
                    refine ⟨1396040420350253342559065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14891097817069368987296693 1396040420350253342559065)
                    ·
                      rfl

theorem cell23_8156337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_8156337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156337 prefixEnd_8156337 := by exact prefixLift 8156337
  have htrace : WordTrace (prefixWord ++ tailWord_8156337) baseStart_8156337 baseEnd_8156337 := by
    simpa [prefixWord, tailWord_8156337, baseEnd_8156337] using wordTrace_append hprefix tailTrace_8156337
  have hstable : (prefixWord ++ tailWord_8156337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156337).length < 2 ^ (prefixWord ++ tailWord_8156337).sum := by decide
  have hdescent : baseEnd_8156337 < baseStart_8156337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156350 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_8156350 : Nat := 118140960795 + 8156350 * 2 ^ 59
def prefixEnd_8156350 : Nat := 4983230072969 + 3 ^ 40 * 8156350 * 2
def baseEnd_8156350 : Nat := 1396042645433089492271545

theorem tailTrace_8156350 : CollatzResearch.WordTrace tailWord_8156350 prefixEnd_8156350 1396042645433089492271545 := by
  unfold tailWord_8156350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37185815500118052315402313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198324349333962945682145669 37185815500118052315402313)
  ·
    refine ⟨27889361625088539236551735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37185815500118052315402313 27889361625088539236551735)
    ·
      refine ⟨41834042437632808854827603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27889361625088539236551735 41834042437632808854827603)
      ·
        refine ⟨62751063656449213282241405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41834042437632808854827603 62751063656449213282241405)
        ·
          refine ⟨23531648871168454980840527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62751063656449213282241405 23531648871168454980840527)
          ·
            refine ⟨35297473306752682471260791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23531648871168454980840527 35297473306752682471260791)
            ·
              refine ⟨52946209960129023706891187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35297473306752682471260791 52946209960129023706891187)
              ·
                refine ⟨79419314940193535560336781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52946209960129023706891187 79419314940193535560336781)
                ·
                  refine ⟨29782243102572575835126293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79419314940193535560336781 29782243102572575835126293)
                  ·
                    refine ⟨1396042645433089492271545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29782243102572575835126293 1396042645433089492271545)
                    ·
                      rfl

theorem cell23_8156350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_8156350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156350 prefixEnd_8156350 := by exact prefixLift 8156350
  have htrace : WordTrace (prefixWord ++ tailWord_8156350) baseStart_8156350 baseEnd_8156350 := by
    simpa [prefixWord, tailWord_8156350, baseEnd_8156350] using wordTrace_append hprefix tailTrace_8156350
  have hstable : (prefixWord ++ tailWord_8156350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156350).length < 2 ^ (prefixWord ++ tailWord_8156350).sum := by decide
  have hdescent : baseEnd_8156350 < baseStart_8156350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156360 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_8156360 : Nat := 118140960795 + 8156360 * 2 ^ 59
def prefixEnd_8156360 : Nat := 4983230072969 + 3 ^ 40 * 8156360 * 2
def baseEnd_8156360 : Nat := 4188133071105813437689589

theorem tailTrace_8156360 : CollatzResearch.WordTrace tailWord_8156360 prefixEnd_8156360 4188133071105813437689589 := by
  unfold tailWord_8156360
  simp only [CollatzResearch.WordTrace]
  refine ⟨148743444365454095115541267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198324592487272126820721689 148743444365454095115541267)
  ·
    refine ⟨223115166548181142673311901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148743444365454095115541267 223115166548181142673311901)
    ·
      refine ⟨83668187455567928502491963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223115166548181142673311901 83668187455567928502491963)
      ·
        refine ⟨125502281183351892753737945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83668187455567928502491963 125502281183351892753737945)
        ·
          refine ⟨94126710887513919565303459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125502281183351892753737945 94126710887513919565303459)
          ·
            refine ⟨141190066331270879347955189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94126710887513919565303459 141190066331270879347955189)
            ·
              refine ⟨13236568718556644938870799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141190066331270879347955189 13236568718556644938870799)
              ·
                refine ⟨19854853077834967408306199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13236568718556644938870799 19854853077834967408306199)
                ·
                  refine ⟨29782279616752451112459299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19854853077834967408306199 29782279616752451112459299)
                  ·
                    refine ⟨44673419425128676668688949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29782279616752451112459299 44673419425128676668688949)
                    ·
                      refine ⟨4188133071105813437689589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44673419425128676668688949 4188133071105813437689589)
                      ·
                        rfl

theorem cell23_8156360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_8156360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156360 prefixEnd_8156360 := by exact prefixLift 8156360
  have htrace : WordTrace (prefixWord ++ tailWord_8156360) baseStart_8156360 baseEnd_8156360 := by
    simpa [prefixWord, tailWord_8156360, baseEnd_8156360] using wordTrace_append hprefix tailTrace_8156360
  have hstable : (prefixWord ++ tailWord_8156360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156360).length < 2 ^ (prefixWord ++ tailWord_8156360).sum := by decide
  have hdescent : baseEnd_8156360 < baseStart_8156360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156370 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_8156370 : Nat := 118140960795 + 8156370 * 2 ^ 59
def prefixEnd_8156370 : Nat := 4983230072969 + 3 ^ 40 * 8156370 * 2
def baseEnd_8156370 : Nat := 4188138205912358398564543

theorem tailTrace_8156370 : CollatzResearch.WordTrace tailWord_8156370 prefixEnd_8156370 4188138205912358398564543 := by
  unfold tailWord_8156370
  simp only [CollatzResearch.WordTrace]
  refine ⟨74371813365217990484736641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198324835640581307959297709 74371813365217990484736641)
  ·
    refine ⟨55778860023913492863552481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74371813365217990484736641 55778860023913492863552481)
    ·
      refine ⟨41834145017935119647664361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55778860023913492863552481 41834145017935119647664361)
      ·
        refine ⟨31375608763451339735748271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41834145017935119647664361 31375608763451339735748271)
        ·
          refine ⟨47063413145177009603622407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31375608763451339735748271 47063413145177009603622407)
          ·
            refine ⟨70595119717765514405433611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47063413145177009603622407 70595119717765514405433611)
            ·
              refine ⟨105892679576648271608150417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70595119717765514405433611 105892679576648271608150417)
              ·
                refine ⟨79419509682486203706112813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105892679576648271608150417 79419509682486203706112813)
                ·
                  refine ⟨29782316130932326389792305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79419509682486203706112813 29782316130932326389792305)
                  ·
                    refine ⟨22336737098199244792344229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29782316130932326389792305 22336737098199244792344229)
                    ·
                      refine ⟨4188138205912358398564543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22336737098199244792344229 4188138205912358398564543)
                      ·
                        rfl

theorem cell23_8156370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_8156370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156370 prefixEnd_8156370 := by exact prefixLift 8156370
  have htrace : WordTrace (prefixWord ++ tailWord_8156370) baseStart_8156370 baseEnd_8156370 := by
    simpa [prefixWord, tailWord_8156370, baseEnd_8156370] using wordTrace_append hprefix tailTrace_8156370
  have hstable : (prefixWord ++ tailWord_8156370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156370).length < 2 ^ (prefixWord ++ tailWord_8156370).sum := by decide
  have hdescent : baseEnd_8156370 < baseStart_8156370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156383 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_8156383 : Nat := 118140960795 + 8156383 * 2 ^ 59
def prefixEnd_8156383 : Nat := 4983230072969 + 3 ^ 40 * 8156383 * 2
def baseEnd_8156383 : Nat := 4188144881160866847701983

theorem tailTrace_8156383 : CollatzResearch.WordTrace tailWord_8156383 prefixEnd_8156383 4188144881160866847701983 := by
  unfold tailWord_8156383
  simp only [CollatzResearch.WordTrace]
  refine ⟨297487727609824865159169803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198325151739883243439446535 297487727609824865159169803)
  ·
    refine ⟨446231591414737297738754705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297487727609824865159169803 446231591414737297738754705)
    ·
      refine ⟨334673693561052973304066029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446231591414737297738754705 334673693561052973304066029)
      ·
        refine ⟨125502635085394864989024761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334673693561052973304066029 125502635085394864989024761)
        ·
          refine ⟨94126976314046148741768571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125502635085394864989024761 94126976314046148741768571)
          ·
            refine ⟨141190464471069223112652857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94126976314046148741768571 141190464471069223112652857)
            ·
              refine ⟨105892848353301917334489643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141190464471069223112652857 105892848353301917334489643)
              ·
                refine ⟨158839272529952876001734465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105892848353301917334489643 158839272529952876001734465)
                ·
                  refine ⟨119129454397464657001300849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158839272529952876001734465 119129454397464657001300849)
                  ·
                    refine ⟨89347090798098492750975637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119129454397464657001300849 89347090798098492750975637)
                    ·
                      refine ⟨4188144881160866847701983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89347090798098492750975637 4188144881160866847701983)
                      ·
                        rfl

theorem cell23_8156383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_8156383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156383 prefixEnd_8156383 := by exact prefixLift 8156383
  have htrace : WordTrace (prefixWord ++ tailWord_8156383) baseStart_8156383 baseEnd_8156383 := by
    simpa [prefixWord, tailWord_8156383, baseEnd_8156383] using wordTrace_append hprefix tailTrace_8156383
  have hstable : (prefixWord ++ tailWord_8156383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156383).length < 2 ^ (prefixWord ++ tailWord_8156383).sum := by decide
  have hdescent : baseEnd_8156383 < baseStart_8156383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156391 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_8156391 : Nat := 118140960795 + 8156391 * 2 ^ 59
def prefixEnd_8156391 : Nat := 4983230072969 + 3 ^ 40 * 8156391 * 2
def baseEnd_8156391 : Nat := 4188148989006102816401947

theorem tailTrace_8156391 : CollatzResearch.WordTrace tailWord_8156391 prefixEnd_8156391 4188148989006102816401947 := by
  unfold tailWord_8156391
  simp only [CollatzResearch.WordTrace]
  refine ⟨297488019393795882525461027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198325346262530588350307351 297488019393795882525461027)
  ·
    refine ⟨446232029090693823788191541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297488019393795882525461027 446232029090693823788191541)
    ·
      refine ⟨41834252727252545980142957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 446232029090693823788191541 41834252727252545980142957)
      ·
        refine ⟨15687844772719704742553609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41834252727252545980142957 15687844772719704742553609)
        ·
          refine ⟨11765883579539778556915207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15687844772719704742553609 11765883579539778556915207)
          ·
            refine ⟨17648825369309667835372811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765883579539778556915207 17648825369309667835372811)
            ·
              refine ⟨26473238053964501753059217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17648825369309667835372811 26473238053964501753059217)
              ·
                refine ⟨19854928540473376314794413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26473238053964501753059217 19854928540473376314794413)
                ·
                  refine ⟨7445598202677516118047905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19854928540473376314794413 7445598202677516118047905)
                  ·
                    refine ⟨5584198652008137088535929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445598202677516118047905 5584198652008137088535929)
                    ·
                      refine ⟨4188148989006102816401947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584198652008137088535929 4188148989006102816401947)
                      ·
                        rfl

theorem cell23_8156391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_8156391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156391 prefixEnd_8156391 := by exact prefixLift 8156391
  have htrace : WordTrace (prefixWord ++ tailWord_8156391) baseStart_8156391 baseEnd_8156391 := by
    simpa [prefixWord, tailWord_8156391, baseEnd_8156391] using wordTrace_append hprefix tailTrace_8156391
  have hstable : (prefixWord ++ tailWord_8156391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156391).length < 2 ^ (prefixWord ++ tailWord_8156391).sum := by decide
  have hdescent : baseEnd_8156391 < baseStart_8156391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156397 : List Nat := [1, 5, 1, 2, 2, 2, 3, 7]
def baseStart_8156397 : Nat := 118140960795 + 8156397 * 2 ^ 59
def prefixEnd_8156397 : Nat := 4983230072969 + 3 ^ 40 * 8156397 * 2
def baseEnd_8156397 : Nat := 155116743329260362700997

theorem tailTrace_8156397 : CollatzResearch.WordTrace tailWord_8156397 prefixEnd_8156397 155116743329260362700997 := by
  unfold tailWord_8156397
  simp only [CollatzResearch.WordTrace]
  refine ⟨297488238231774145550179445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198325492154516097033452963 297488238231774145550179445)
  ·
    refine ⟨27889522334228826145329323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297488238231774145550179445 27889522334228826145329323)
    ·
      refine ⟨41834283501343239217993985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27889522334228826145329323 41834283501343239217993985)
      ·
        refine ⟨31375712626007429413495489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41834283501343239217993985 31375712626007429413495489)
        ·
          refine ⟨23531784469505572060121617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31375712626007429413495489 23531784469505572060121617)
          ·
            refine ⟨17648838352129179045091213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23531784469505572060121617 17648838352129179045091213)
            ·
              refine ⟨6618314382048442141909205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17648838352129179045091213 6618314382048442141909205)
              ·
                refine ⟨155116743329260362700997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6618314382048442141909205 155116743329260362700997)
                ·
                  rfl

theorem cell23_8156397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 7].length) (baseStart_8156397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156397 prefixEnd_8156397 := by exact prefixLift 8156397
  have htrace : WordTrace (prefixWord ++ tailWord_8156397) baseStart_8156397 baseEnd_8156397 := by
    simpa [prefixWord, tailWord_8156397, baseEnd_8156397] using wordTrace_append hprefix tailTrace_8156397
  have hstable : (prefixWord ++ tailWord_8156397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156397).length < 2 ^ (prefixWord ++ tailWord_8156397).sum := by decide
  have hdescent : baseEnd_8156397 < baseStart_8156397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156418 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_8156418 : Nat := 118140960795 + 8156418 * 2 ^ 59
def prefixEnd_8156418 : Nat := 4983230072969 + 3 ^ 40 * 8156418 * 2
def baseEnd_8156418 : Nat := 1396054284327924736921441

theorem tailTrace_8156418 : CollatzResearch.WordTrace tailWord_8156418 prefixEnd_8156418 1396054284327924736921441 := by
  unfold tailWord_8156418
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372251041174516534173477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198326002776465377424462605 74372251041174516534173477)
  ·
    refine ⟨13944797070220221850157527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74372251041174516534173477 13944797070220221850157527)
    ·
      refine ⟨20917195605330332775236291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13944797070220221850157527 20917195605330332775236291)
      ·
        refine ⟨31375793407995499162854437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20917195605330332775236291 31375793407995499162854437)
        ·
          refine ⟨5882961263999156093035207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31375793407995499162854437 5882961263999156093035207)
          ·
            refine ⟨8824441895998734139552811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882961263999156093035207 8824441895998734139552811)
            ·
              refine ⟨13236662843998101209329217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8824441895998734139552811 13236662843998101209329217)
              ·
                refine ⟨9927497132998575906996913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13236662843998101209329217 9927497132998575906996913)
                ·
                  refine ⟨7445622849748931930247685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9927497132998575906996913 7445622849748931930247685)
                  ·
                    refine ⟨1396054284327924736921441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445622849748931930247685 1396054284327924736921441)
                    ·
                      rfl

theorem cell23_8156418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_8156418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156418 prefixEnd_8156418 := by exact prefixLift 8156418
  have htrace : WordTrace (prefixWord ++ tailWord_8156418) baseStart_8156418 baseEnd_8156418 := by
    simpa [prefixWord, tailWord_8156418, baseEnd_8156418] using wordTrace_append hprefix tailTrace_8156418
  have hstable : (prefixWord ++ tailWord_8156418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156418).length < 2 ^ (prefixWord ++ tailWord_8156418).sum := by decide
  have hdescent : baseEnd_8156418 < baseStart_8156418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156424 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_8156424 : Nat := 118140960795 + 8156424 * 2 ^ 59
def prefixEnd_8156424 : Nat := 4983230072969 + 3 ^ 40 * 8156424 * 2
def baseEnd_8156424 : Nat := 4188165933867701187289295

theorem tailTrace_8156424 : CollatzResearch.WordTrace tailWord_8156424 prefixEnd_8156424 4188165933867701187289295 := by
  unfold tailWord_8156424
  simp only [CollatzResearch.WordTrace]
  refine ⟨148744611501338164580706163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198326148668450886107608217 148744611501338164580706163)
  ·
    refine ⟨223116917252007246871059245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148744611501338164580706163 223116917252007246871059245)
    ·
      refine ⟨83668843969502717576647217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223116917252007246871059245 83668843969502717576647217)
      ·
        refine ⟨62751632977127038182485413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83668843969502717576647217 62751632977127038182485413)
        ·
          refine ⟨11765931183211319659216015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62751632977127038182485413 11765931183211319659216015)
          ·
            refine ⟨17648896774816979488824023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765931183211319659216015 17648896774816979488824023)
            ·
              refine ⟨26473345162225469233236035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17648896774816979488824023 26473345162225469233236035)
              ·
                refine ⟨39710017743338203849854053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26473345162225469233236035 39710017743338203849854053)
                ·
                  refine ⟨7445628326875913221847635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39710017743338203849854053 7445628326875913221847635)
                  ·
                    refine ⟨11168442490313869832771453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7445628326875913221847635 11168442490313869832771453)
                    ·
                      refine ⟨4188165933867701187289295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11168442490313869832771453 4188165933867701187289295)
                      ·
                        rfl

theorem cell23_8156424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_8156424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156424 prefixEnd_8156424 := by exact prefixLift 8156424
  have htrace : WordTrace (prefixWord ++ tailWord_8156424) baseStart_8156424 baseEnd_8156424 := by
    simpa [prefixWord, tailWord_8156424, baseEnd_8156424] using wordTrace_append hprefix tailTrace_8156424
  have hstable : (prefixWord ++ tailWord_8156424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156424).length < 2 ^ (prefixWord ++ tailWord_8156424).sum := by decide
  have hdescent : baseEnd_8156424 < baseStart_8156424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156440 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_8156440 : Nat := 118140960795 + 8156440 * 2 ^ 59
def prefixEnd_8156440 : Nat := 4983230072969 + 3 ^ 40 * 8156440 * 2
def baseEnd_8156440 : Nat := 1396058049852724374896407

theorem tailTrace_8156440 : CollatzResearch.WordTrace tailWord_8156440 prefixEnd_8156440 1396058049852724374896407 := by
  unfold tailWord_8156440
  simp only [CollatzResearch.WordTrace]
  refine ⟨148744903285309181946997387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198326537713745575929329849 148744903285309181946997387)
  ·
    refine ⟨223117354927963772920496081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148744903285309181946997387 223117354927963772920496081)
    ·
      refine ⟨167338016195972829690372061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223117354927963772920496081 167338016195972829690372061)
      ·
        refine ⟨62751756073489811133889523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167338016195972829690372061 62751756073489811133889523)
        ·
          refine ⟨94127634110234716700834285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62751756073489811133889523 94127634110234716700834285)
          ·
            refine ⟨35297862791338018762812857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94127634110234716700834285 35297862791338018762812857)
            ·
              refine ⟨26473397093503514072109643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35297862791338018762812857 26473397093503514072109643)
              ·
                refine ⟨39710095640255271108164465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26473397093503514072109643 39710095640255271108164465)
                ·
                  refine ⟨29782571730191453331123349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39710095640255271108164465 29782571730191453331123349)
                  ·
                    refine ⟨1396058049852724374896407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29782571730191453331123349 1396058049852724374896407)
                    ·
                      rfl

theorem cell23_8156440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_8156440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156440 prefixEnd_8156440 := by exact prefixLift 8156440
  have htrace : WordTrace (prefixWord ++ tailWord_8156440) baseStart_8156440 baseEnd_8156440 := by
    simpa [prefixWord, tailWord_8156440, baseEnd_8156440] using wordTrace_append hprefix tailTrace_8156440
  have hstable : (prefixWord ++ tailWord_8156440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156440).length < 2 ^ (prefixWord ++ tailWord_8156440).sum := by decide
  have hdescent : baseEnd_8156440 < baseStart_8156440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156481 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8156481 : Nat := 118140960795 + 8156481 * 2 ^ 59
def prefixEnd_8156481 : Nat := 4983230072969 + 3 ^ 40 * 8156481 * 2
def baseEnd_8156481 : Nat := 4188195202265007464276533

theorem tailTrace_8156481 : CollatzResearch.WordTrace tailWord_8156481 prefixEnd_8156481 4188195202265007464276533 := by
  unfold tailWord_8156481
  simp only [CollatzResearch.WordTrace]
  refine ⟨297491301963469827896237297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198327534642313218597491531 297491301963469827896237297)
  ·
    refine ⟨223118476472602370922177973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297491301963469827896237297 223118476472602370922177973)
    ·
      refine ⟨20917357169306472273954185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223118476472602370922177973 20917357169306472273954185)
      ·
        refine ⟨15688017876979854205465639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20917357169306472273954185 15688017876979854205465639)
        ·
          refine ⟨23532026815469781308198459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15688017876979854205465639 23532026815469781308198459)
          ·
            refine ⟨35298040223204671962297689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23532026815469781308198459 35298040223204671962297689)
            ·
              refine ⟨26473530167403503971723267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35298040223204671962297689 26473530167403503971723267)
              ·
                refine ⟨39710295251105255957584901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26473530167403503971723267 39710295251105255957584901)
                ·
                  refine ⟨7445680359582235492047169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39710295251105255957584901 7445680359582235492047169)
                  ·
                    refine ⟨5584260269686676619035377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445680359582235492047169 5584260269686676619035377)
                    ·
                      refine ⟨4188195202265007464276533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584260269686676619035377 4188195202265007464276533)
                      ·
                        rfl

theorem cell23_8156481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8156481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156481 prefixEnd_8156481 := by exact prefixLift 8156481
  have htrace : WordTrace (prefixWord ++ tailWord_8156481) baseStart_8156481 baseEnd_8156481 := by
    simpa [prefixWord, tailWord_8156481, baseEnd_8156481] using wordTrace_append hprefix tailTrace_8156481
  have hstable : (prefixWord ++ tailWord_8156481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156481).length < 2 ^ (prefixWord ++ tailWord_8156481).sum := by decide
  have hdescent : baseEnd_8156481 < baseStart_8156481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156487 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 7]
def baseStart_8156487 : Nat := 118140960795 + 8156487 * 2 ^ 59
def prefixEnd_8156487 : Nat := 4983230072969 + 3 ^ 40 * 8156487 * 2
def baseEnd_8156487 : Nat := 465355364794326048977945

theorem tailTrace_8156487 : CollatzResearch.WordTrace tailWord_8156487 prefixEnd_8156487 465355364794326048977945 := by
  unfold tailWord_8156487
  simp only [CollatzResearch.WordTrace]
  refine ⟨297491520801448090920955715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198327680534298727280637143 297491520801448090920955715)
  ·
    refine ⟨446237281202172136381433573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297491520801448090920955715 446237281202172136381433573)
    ·
      refine ⟨83669490225407275571518795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446237281202172136381433573 83669490225407275571518795)
      ·
        refine ⟨125504235338110913357278193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83669490225407275571518795 125504235338110913357278193)
        ·
          refine ⟨94128176503583185017958645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125504235338110913357278193 94128176503583185017958645)
          ·
            refine ⟨8824516547210923595433623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94128176503583185017958645 8824516547210923595433623)
            ·
              refine ⟨13236774820816385393150435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8824516547210923595433623 13236774820816385393150435)
              ·
                refine ⟨19855162231224578089725653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13236774820816385393150435 19855162231224578089725653)
                ·
                  refine ⟨465355364794326048977945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19855162231224578089725653 465355364794326048977945)
                  ·
                    rfl

theorem cell23_8156487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 7].length) (baseStart_8156487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156487 prefixEnd_8156487 := by exact prefixLift 8156487
  have htrace : WordTrace (prefixWord ++ tailWord_8156487) baseStart_8156487 baseEnd_8156487 := by
    simpa [prefixWord, tailWord_8156487, baseEnd_8156487] using wordTrace_append hprefix tailTrace_8156487
  have hstable : (prefixWord ++ tailWord_8156487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156487).length < 2 ^ (prefixWord ++ tailWord_8156487).sum := by decide
  have hdescent : baseEnd_8156487 < baseStart_8156487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156517 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_8156517 : Nat := 118140960795 + 8156517 * 2 ^ 59
def prefixEnd_8156517 : Nat := 4983230072969 + 3 ^ 40 * 8156517 * 2
def baseEnd_8156517 : Nat := 1396071229189523107808789

theorem tailTrace_8156517 : CollatzResearch.WordTrace tailWord_8156517 prefixEnd_8156517 1396071229189523107808789 := by
  unfold tailWord_8156517
  simp only [CollatzResearch.WordTrace]
  refine ⟨297492614991339406044547805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198328409994226270696365203 297492614991339406044547805)
  ·
    refine ⟨111559730621752277266705427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297492614991339406044547805 111559730621752277266705427)
    ·
      refine ⟨167339595932628415900058141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111559730621752277266705427 167339595932628415900058141)
      ·
        refine ⟨62752348474735655962521803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167339595932628415900058141 62752348474735655962521803)
        ·
          refine ⟨94128522712103483943782705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62752348474735655962521803 94128522712103483943782705)
          ·
            refine ⟨70596392034077612957837029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94128522712103483943782705 70596392034077612957837029)
            ·
              refine ⟨13236823506389552429594443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70596392034077612957837029 13236823506389552429594443)
              ·
                refine ⟨19855235259584328644391665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13236823506389552429594443 19855235259584328644391665)
                ·
                  refine ⟨14891426444688246483293749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19855235259584328644391665 14891426444688246483293749)
                  ·
                    refine ⟨1396071229189523107808789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14891426444688246483293749 1396071229189523107808789)
                    ·
                      rfl

theorem cell23_8156517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_8156517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156517 prefixEnd_8156517 := by exact prefixLift 8156517
  have htrace : WordTrace (prefixWord ++ tailWord_8156517) baseStart_8156517 baseEnd_8156517 := by
    simpa [prefixWord, tailWord_8156517, baseEnd_8156517] using wordTrace_append hprefix tailTrace_8156517
  have hstable : (prefixWord ++ tailWord_8156517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156517).length < 2 ^ (prefixWord ++ tailWord_8156517).sum := by decide
  have hdescent : baseEnd_8156517 < baseStart_8156517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156537 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_8156537 : Nat := 118140960795 + 8156537 * 2 ^ 59
def prefixEnd_8156537 : Nat := 4983230072969 + 3 ^ 40 * 8156537 * 2
def baseEnd_8156537 : Nat := 4188223957181659245176275

theorem tailTrace_8156537 : CollatzResearch.WordTrace tailWord_8156537 prefixEnd_8156537 4188223957181659245176275 := by
  unfold tailWord_8156537
  simp only [CollatzResearch.WordTrace]
  refine ⟨297493344451266949460275865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198328896300844632973517243 297493344451266949460275865)
  ·
    refine ⟨223120008338450212095206899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297493344451266949460275865 223120008338450212095206899)
    ·
      refine ⟨334680012507675318142810349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223120008338450212095206899 334680012507675318142810349)
      ·
        refine ⟨125505004690378244303553881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334680012507675318142810349 125505004690378244303553881)
        ·
          refine ⟨94128753517783683227665411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125505004690378244303553881 94128753517783683227665411)
          ·
            refine ⟨141193130276675524841498117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94128753517783683227665411 141193130276675524841498117)
            ·
              refine ⟨26473711926876660907780897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141193130276675524841498117 26473711926876660907780897)
              ·
                refine ⟨19855283945157495680835673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26473711926876660907780897 19855283945157495680835673)
                ·
                  refine ⟨14891462958868121760626755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19855283945157495680835673 14891462958868121760626755)
                  ·
                    refine ⟨22337194438302182640940133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14891462958868121760626755 22337194438302182640940133)
                    ·
                      refine ⟨4188223957181659245176275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22337194438302182640940133 4188223957181659245176275)
                      ·
                        rfl

theorem cell23_8156537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_8156537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156537 prefixEnd_8156537 := by exact prefixLift 8156537
  have htrace : WordTrace (prefixWord ++ tailWord_8156537) baseStart_8156537 baseEnd_8156537 := by
    simpa [prefixWord, tailWord_8156537, baseEnd_8156537] using wordTrace_append hprefix tailTrace_8156537
  have hstable : (prefixWord ++ tailWord_8156537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156537).length < 2 ^ (prefixWord ++ tailWord_8156537).sum := by decide
  have hdescent : baseEnd_8156537 < baseStart_8156537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156540 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_8156540 : Nat := 118140960795 + 8156540 * 2 ^ 59
def prefixEnd_8156540 : Nat := 4983230072969 + 3 ^ 40 * 8156540 * 2
def baseEnd_8156540 : Nat := 4188225497623622733438761

theorem tailTrace_8156540 : CollatzResearch.WordTrace tailWord_8156540 prefixEnd_8156540 4188225497623622733438761 := by
  unfold tailWord_8156540
  simp only [CollatzResearch.WordTrace]
  refine ⟨148746726935128040486317537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198328969246837387315090049 148746726935128040486317537)
  ·
    refine ⟨111560045201346030364738153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148746726935128040486317537 111560045201346030364738153)
    ·
      refine ⟨83670033901009522773553615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111560045201346030364738153 83670033901009522773553615)
      ·
        refine ⟨125505050851514284160330423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83670033901009522773553615 125505050851514284160330423)
        ·
          refine ⟨188257576277271426240495635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125505050851514284160330423 188257576277271426240495635)
          ·
            refine ⟨282386364415907139360743453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188257576277271426240495635 282386364415907139360743453)
            ·
              refine ⟨105894886655965177260278795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282386364415907139360743453 105894886655965177260278795)
              ·
                refine ⟨158842329983947765890418193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105894886655965177260278795 158842329983947765890418193)
                ·
                  refine ⟨119131747487960824417813645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158842329983947765890418193 119131747487960824417813645)
                  ·
                    refine ⟨44674405307985309156680117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119131747487960824417813645 44674405307985309156680117)
                    ·
                      refine ⟨4188225497623622733438761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44674405307985309156680117 4188225497623622733438761)
                      ·
                        rfl

theorem cell23_8156540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_8156540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156540 prefixEnd_8156540 := by exact prefixLift 8156540
  have htrace : WordTrace (prefixWord ++ tailWord_8156540) baseStart_8156540 baseEnd_8156540 := by
    simpa [prefixWord, tailWord_8156540, baseEnd_8156540] using wordTrace_append hprefix tailTrace_8156540
  have hstable : (prefixWord ++ tailWord_8156540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156540).length < 2 ^ (prefixWord ++ tailWord_8156540).sum := by decide
  have hdescent : baseEnd_8156540 < baseStart_8156540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156564 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_8156564 : Nat := 118140960795 + 8156564 * 2 ^ 59
def prefixEnd_8156564 : Nat := 4983230072969 + 3 ^ 40 * 8156564 * 2
def baseEnd_8156564 : Nat := 1396079273719776879846217

theorem tailTrace_8156564 : CollatzResearch.WordTrace tailWord_8156564 prefixEnd_8156564 1396079273719776879846217 := by
  unfold tailWord_8156564
  simp only [CollatzResearch.WordTrace]
  refine ⟨148747164611084566535754373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198329552814779422047672497 148747164611084566535754373)
  ·
    refine ⟨27890093364578356225453945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148747164611084566535754373 27890093364578356225453945)
    ·
      refine ⟨20917570023433767169090459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27890093364578356225453945 20917570023433767169090459)
      ·
        refine ⟨31376355035150650753635689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20917570023433767169090459 31376355035150650753635689)
        ·
          refine ⟨23532266276362988065226767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31376355035150650753635689 23532266276362988065226767)
          ·
            refine ⟨35298399414544482097840151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23532266276362988065226767 35298399414544482097840151)
            ·
              refine ⟨52947599121816723146760227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35298399414544482097840151 52947599121816723146760227)
              ·
                refine ⟨79421398682725084720140341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52947599121816723146760227 79421398682725084720140341)
                ·
                  refine ⟨7445756126505476692513157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79421398682725084720140341 7445756126505476692513157)
                  ·
                    refine ⟨1396079273719776879846217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445756126505476692513157 1396079273719776879846217)
                    ·
                      rfl

theorem cell23_8156564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_8156564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156564 prefixEnd_8156564 := by exact prefixLift 8156564
  have htrace : WordTrace (prefixWord ++ tailWord_8156564) baseStart_8156564 baseEnd_8156564 := by
    simpa [prefixWord, tailWord_8156564, baseEnd_8156564] using wordTrace_append hprefix tailTrace_8156564
  have hstable : (prefixWord ++ tailWord_8156564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156564).length < 2 ^ (prefixWord ++ tailWord_8156564).sum := by decide
  have hdescent : baseEnd_8156564 < baseStart_8156564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156597 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_8156597 : Nat := 118140960795 + 8156597 * 2 ^ 59
def prefixEnd_8156597 : Nat := 4983230072969 + 3 ^ 40 * 8156597 * 2
def baseEnd_8156597 : Nat := 4188254766020929010425999

theorem tailTrace_8156597 : CollatzResearch.WordTrace tailWord_8156597 prefixEnd_8156597 4188254766020929010425999 := by
  unfold tailWord_8156597
  simp only [CollatzResearch.WordTrace]
  refine ⟨297495532831049579707460045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198330355220699719804973363 297495532831049579707460045)
  ·
    refine ⟨111560824811643592390297517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297495532831049579707460045 111560824811643592390297517)
    ·
      refine ⟨41835309304366347146361569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111560824811643592390297517 41835309304366347146361569)
      ·
        refine ⟨31376481978274760359771177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41835309304366347146361569 31376481978274760359771177)
        ·
          refine ⟨23532361483706070269828383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31376481978274760359771177 23532361483706070269828383)
          ·
            refine ⟨35298542225559105404742575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23532361483706070269828383 35298542225559105404742575)
            ·
              refine ⟨52947813338338658107113863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35298542225559105404742575 52947813338338658107113863)
              ·
                refine ⟨79421720007507987160670795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52947813338338658107113863 79421720007507987160670795)
                ·
                  refine ⟨119132580011261980741006193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79421720007507987160670795 119132580011261980741006193)
                  ·
                    refine ⟨89349435008446485555754645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119132580011261980741006193 89349435008446485555754645)
                    ·
                      refine ⟨4188254766020929010425999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89349435008446485555754645 4188254766020929010425999)
                      ·
                        rfl

theorem cell23_8156597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_8156597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156597 prefixEnd_8156597 := by exact prefixLift 8156597
  have htrace : WordTrace (prefixWord ++ tailWord_8156597) baseStart_8156597 baseEnd_8156597 := by
    simpa [prefixWord, tailWord_8156597, baseEnd_8156597] using wordTrace_append hprefix tailTrace_8156597
  have hstable : (prefixWord ++ tailWord_8156597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156597).length < 2 ^ (prefixWord ++ tailWord_8156597).sum := by decide
  have hdescent : baseEnd_8156597 < baseStart_8156597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156654 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_8156654 : Nat := 118140960795 + 8156654 * 2 ^ 59
def prefixEnd_8156654 : Nat := 4983230072969 + 3 ^ 40 * 8156654 * 2
def baseEnd_8156654 : Nat := 1396094678139411762471079

theorem tailTrace_8156654 : CollatzResearch.WordTrace tailWord_8156654 prefixEnd_8156654 1396094678139411762471079 := by
  unfold tailWord_8156654
  simp only [CollatzResearch.WordTrace]
  refine ⟨37187201473980384805285627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198331741194562052294856677 37187201473980384805285627)
  ·
    refine ⟨55780802210970577207928441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37187201473980384805285627 55780802210970577207928441)
    ·
      refine ⟨41835601658227932905946331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55780802210970577207928441 41835601658227932905946331)
      ·
        refine ⟨62753402487341899358919497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41835601658227932905946331 62753402487341899358919497)
        ·
          refine ⟨47065051865506424519189623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62753402487341899358919497 47065051865506424519189623)
          ·
            refine ⟨70597577798259636778784435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47065051865506424519189623 70597577798259636778784435)
            ·
              refine ⟨105896366697389455168176653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70597577798259636778784435 105896366697389455168176653)
              ·
                refine ⟨39711137511521045688066245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105896366697389455168176653 39711137511521045688066245)
                ·
                  refine ⟨7445838283410196066512421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39711137511521045688066245 7445838283410196066512421)
                  ·
                    refine ⟨1396094678139411762471079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445838283410196066512421 1396094678139411762471079)
                    ·
                      rfl

theorem cell23_8156654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_8156654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156654 prefixEnd_8156654 := by exact prefixLift 8156654
  have htrace : WordTrace (prefixWord ++ tailWord_8156654) baseStart_8156654 baseEnd_8156654 := by
    simpa [prefixWord, tailWord_8156654, baseEnd_8156654] using wordTrace_append hprefix tailTrace_8156654
  have hstable : (prefixWord ++ tailWord_8156654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156654).length < 2 ^ (prefixWord ++ tailWord_8156654).sum := by decide
  have hdescent : baseEnd_8156654 < baseStart_8156654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156657 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_8156657 : Nat := 118140960795 + 8156657 * 2 ^ 59
def prefixEnd_8156657 : Nat := 4983230072969 + 3 ^ 40 * 8156657 * 2
def baseEnd_8156657 : Nat := 4188285574860198775675723

theorem tailTrace_8156657 : CollatzResearch.WordTrace tailWord_8156657 prefixEnd_8156657 4188285574860198775675723 := by
  unfold tailWord_8156657
  simp only [CollatzResearch.WordTrace]
  refine ⟨297497721210832209954644225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198331814140554806636429483 297497721210832209954644225)
  ·
    refine ⟨223123290908124157465983169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297497721210832209954644225 223123290908124157465983169)
    ·
      refine ⟨167342468181093118099487377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223123290908124157465983169 167342468181093118099487377)
      ·
        refine ⟨125506851135819838574615533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167342468181093118099487377 125506851135819838574615533)
        ·
          refine ⟨47065069175932439465480825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125506851135819838574615533 47065069175932439465480825)
          ·
            refine ⟨35298801881949329599110619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47065069175932439465480825 35298801881949329599110619)
            ·
              refine ⟨52948202822923994398665929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35298801881949329599110619 52948202822923994398665929)
              ·
                refine ⟨39711152117192995798999447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52948202822923994398665929 39711152117192995798999447)
                ·
                  refine ⟨59566728175789493698499171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39711152117192995798999447 59566728175789493698499171)
                  ·
                    refine ⟨89350092263684240547748757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59566728175789493698499171 89350092263684240547748757)
                    ·
                      refine ⟨4188285574860198775675723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89350092263684240547748757 4188285574860198775675723)
                      ·
                        rfl

theorem cell23_8156657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_8156657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156657 prefixEnd_8156657 := by exact prefixLift 8156657
  have htrace : WordTrace (prefixWord ++ tailWord_8156657) baseStart_8156657 baseEnd_8156657 := by
    simpa [prefixWord, tailWord_8156657, baseEnd_8156657] using wordTrace_append hprefix tailTrace_8156657
  have hstable : (prefixWord ++ tailWord_8156657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156657).length < 2 ^ (prefixWord ++ tailWord_8156657).sum := by decide
  have hdescent : baseEnd_8156657 < baseStart_8156657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156712 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_8156712 : Nat := 118140960795 + 8156712 * 2 ^ 59
def prefixEnd_8156712 : Nat := 4983230072969 + 3 ^ 40 * 8156712 * 2
def baseEnd_8156712 : Nat := 4188313816296196060487971

theorem tailTrace_8156712 : CollatzResearch.WordTrace tailWord_8156712 prefixEnd_8156712 4188313816296196060487971 := by
  unfold tailWord_8156712
  simp only [CollatzResearch.WordTrace]
  refine ⟨148749863612816477173948195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198333151483755302898597593 148749863612816477173948195)
  ·
    refine ⟨223124795419224715760922293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148749863612816477173948195 223124795419224715760922293)
    ·
      refine ⟨20917949570552317102586465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223124795419224715760922293 20917949570552317102586465)
      ·
        refine ⟨15688462177914237826939849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20917949570552317102586465 15688462177914237826939849)
        ·
          refine ⟨11766346633435678370204887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15688462177914237826939849 11766346633435678370204887)
          ·
            refine ⟨17649519950153517555307331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766346633435678370204887 17649519950153517555307331)
            ·
              refine ⟨26474279925230276332960997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17649519950153517555307331 26474279925230276332960997)
              ·
                refine ⟨4963927485980676812430187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26474279925230276332960997 4963927485980676812430187)
                ·
                  refine ⟨7445891228971015218645281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963927485980676812430187 7445891228971015218645281)
                  ·
                    refine ⟨5584418421728261413983961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445891228971015218645281 5584418421728261413983961)
                    ·
                      refine ⟨4188313816296196060487971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584418421728261413983961 4188313816296196060487971)
                      ·
                        rfl

theorem cell23_8156712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_8156712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156712 prefixEnd_8156712 := by exact prefixLift 8156712
  have htrace : WordTrace (prefixWord ++ tailWord_8156712) baseStart_8156712 baseEnd_8156712 := by
    simpa [prefixWord, tailWord_8156712, baseEnd_8156712] using wordTrace_append hprefix tailTrace_8156712
  have hstable : (prefixWord ++ tailWord_8156712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156712).length < 2 ^ (prefixWord ++ tailWord_8156712).sum := by decide
  have hdescent : baseEnd_8156712 < baseStart_8156712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156727 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 8]
def baseStart_8156727 : Nat := 118140960795 + 8156727 * 2 ^ 59
def prefixEnd_8156727 : Nat := 4983230072969 + 3 ^ 40 * 8156727 * 2
def baseEnd_8156727 : Nat := 1396107172835337833933467

theorem tailTrace_8156727 : CollatzResearch.WordTrace tailWord_8156727 prefixEnd_8156727 1396107172835337833933467 := by
  unfold tailWord_8156727
  simp only [CollatzResearch.WordTrace]
  refine ⟨297500274320578611909692435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198333516213719074606461623 297500274320578611909692435)
  ·
    refine ⟨446250411480867917864538653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297500274320578611909692435 446250411480867917864538653)
    ·
      refine ⟨167343904305325469199201995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446250411480867917864538653 167343904305325469199201995)
      ·
        refine ⟨251015856457988203798802993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167343904305325469199201995 251015856457988203798802993)
        ·
          refine ⟨188261892343491152849102245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251015856457988203798802993 188261892343491152849102245)
          ·
            refine ⟨35299104814404591159206671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188261892343491152849102245 35299104814404591159206671)
            ·
              refine ⟨52948657221606886738810007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35299104814404591159206671 52948657221606886738810007)
              ·
                refine ⟨79422985832410330108215011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52948657221606886738810007 79422985832410330108215011)
                ·
                  refine ⟨119134478748615495162322517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79422985832410330108215011 119134478748615495162322517)
                  ·
                    refine ⟨1396107172835337833933467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119134478748615495162322517 1396107172835337833933467)
                    ·
                      rfl

theorem cell23_8156727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_8156727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156727 prefixEnd_8156727 := by exact prefixLift 8156727
  have htrace : WordTrace (prefixWord ++ tailWord_8156727) baseStart_8156727 baseEnd_8156727 := by
    simpa [prefixWord, tailWord_8156727, baseEnd_8156727] using wordTrace_append hprefix tailTrace_8156727
  have hstable : (prefixWord ++ tailWord_8156727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156727).length < 2 ^ (prefixWord ++ tailWord_8156727).sum := by decide
  have hdescent : baseEnd_8156727 < baseStart_8156727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156747 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4]
def baseStart_8156747 : Nat := 118140960795 + 8156747 * 2 ^ 59
def prefixEnd_8156747 : Nat := 4983230072969 + 3 ^ 40 * 8156747 * 2
def baseEnd_8156747 : Nat := 4188331788119103423550309

theorem tailTrace_8156747 : CollatzResearch.WordTrace tailWord_8156747 prefixEnd_8156747 4188331788119103423550309 := by
  unfold tailWord_8156747
  simp only [CollatzResearch.WordTrace]
  refine ⟨297501003780506155325420495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198334002520337436883613663 297501003780506155325420495)
  ·
    refine ⟨446251505670759232988130743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297501003780506155325420495 446251505670759232988130743)
    ·
      refine ⟨669377258506138849482196115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446251505670759232988130743 669377258506138849482196115)
      ·
        refine ⟨1004065887759208274223294173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669377258506138849482196115 1004065887759208274223294173)
        ·
          refine ⟨376524707909703102833735315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004065887759208274223294173 376524707909703102833735315)
          ·
            refine ⟨564787061864554654250602973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376524707909703102833735315 564787061864554654250602973)
            ·
              refine ⟨211795148199207995343976115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564787061864554654250602973 211795148199207995343976115)
              ·
                refine ⟨317692722298811993015964173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211795148199207995343976115 317692722298811993015964173)
                ·
                  refine ⟨119134770862054497380986565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317692722298811993015964173 119134770862054497380986565)
                  ·
                    refine ⟨22337769536635218258934981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119134770862054497380986565 22337769536635218258934981)
                    ·
                      refine ⟨4188331788119103423550309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22337769536635218258934981 4188331788119103423550309)
                      ·
                        rfl

theorem cell23_8156747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_8156747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156747 prefixEnd_8156747 := by exact prefixLift 8156747
  have htrace : WordTrace (prefixWord ++ tailWord_8156747) baseStart_8156747 baseEnd_8156747 := by
    simpa [prefixWord, tailWord_8156747, baseEnd_8156747] using wordTrace_append hprefix tailTrace_8156747
  have hstable : (prefixWord ++ tailWord_8156747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156747).length < 2 ^ (prefixWord ++ tailWord_8156747).sum := by decide
  have hdescent : baseEnd_8156747 < baseStart_8156747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156751 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 4, 2, 2]
def baseStart_8156751 : Nat := 118140960795 + 8156751 * 2 ^ 59
def prefixEnd_8156751 : Nat := 4983230072969 + 3 ^ 40 * 8156751 * 2
def baseEnd_8156751 : Nat := 4188333842041721407900291

theorem tailTrace_8156751 : CollatzResearch.WordTrace tailWord_8156751 prefixEnd_8156751 4188333842041721407900291 := by
  unfold tailWord_8156751
  simp only [CollatzResearch.WordTrace]
  refine ⟨297501149672491664008566107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198334099781661109339044071 297501149672491664008566107)
  ·
    refine ⟨446251724508737496012849161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297501149672491664008566107 446251724508737496012849161)
    ·
      refine ⟨334688793381553122009636871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446251724508737496012849161 334688793381553122009636871)
      ·
        refine ⟨502033190072329683014455307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334688793381553122009636871 502033190072329683014455307)
        ·
          refine ⟨753049785108494524521682961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502033190072329683014455307 753049785108494524521682961)
          ·
            refine ⟨564787338831370893391262221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753049785108494524521682961 564787338831370893391262221)
            ·
              refine ⟨211795252061764085021723333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564787338831370893391262221 211795252061764085021723333)
              ·
                refine ⟨39711609761580765941573125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211795252061764085021723333 39711609761580765941573125)
                ·
                  refine ⟨7445926830296393614044961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39711609761580765941573125 7445926830296393614044961)
                  ·
                    refine ⟨5584445122722295210533721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445926830296393614044961 5584445122722295210533721)
                    ·
                      refine ⟨4188333842041721407900291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584445122722295210533721 4188333842041721407900291)
                      ·
                        rfl

theorem cell23_8156751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 2, 2].length) (baseStart_8156751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156751 prefixEnd_8156751 := by exact prefixLift 8156751
  have htrace : WordTrace (prefixWord ++ tailWord_8156751) baseStart_8156751 baseEnd_8156751 := by
    simpa [prefixWord, tailWord_8156751, baseEnd_8156751] using wordTrace_append hprefix tailTrace_8156751
  have hstable : (prefixWord ++ tailWord_8156751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156751).length < 2 ^ (prefixWord ++ tailWord_8156751).sum := by decide
  have hdescent : baseEnd_8156751 < baseStart_8156751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156757 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 11]
def baseStart_8156757 : Nat := 118140960795 + 8156757 * 2 ^ 59
def prefixEnd_8156757 : Nat := 4983230072969 + 3 ^ 40 * 8156757 * 2
def baseEnd_8156757 : Nat := 465370769213960931602807

theorem tailTrace_8156757 : CollatzResearch.WordTrace tailWord_8156757 prefixEnd_8156757 465370769213960931602807 := by
  unfold tailWord_8156757
  simp only [CollatzResearch.WordTrace]
  refine ⟨297501368510469927033284525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198334245673646618022189683 297501368510469927033284525)
  ·
    refine ⟨111563013191426222637481697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297501368510469927033284525 111563013191426222637481697)
    ·
      refine ⟨83672259893569666978111273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111563013191426222637481697 83672259893569666978111273)
      ·
        refine ⟨62754194920177250233583455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83672259893569666978111273 62754194920177250233583455)
        ·
          refine ⟨94131292380265875350375183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62754194920177250233583455 94131292380265875350375183)
          ·
            refine ⟨141196938570398813025562775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94131292380265875350375183 141196938570398813025562775)
            ·
              refine ⟨211795407855598219538344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141196938570398813025562775 211795407855598219538344163)
              ·
                refine ⟨317693111783397329307516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211795407855598219538344163 317693111783397329307516245)
                ·
                  refine ⟨465370769213960931602807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 317693111783397329307516245 465370769213960931602807)
                  ·
                    rfl

theorem cell23_8156757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_8156757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156757 prefixEnd_8156757 := by exact prefixLift 8156757
  have htrace : WordTrace (prefixWord ++ tailWord_8156757) baseStart_8156757 baseEnd_8156757 := by
    simpa [prefixWord, tailWord_8156757, baseEnd_8156757] using wordTrace_append hprefix tailTrace_8156757
  have hstable : (prefixWord ++ tailWord_8156757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156757).length < 2 ^ (prefixWord ++ tailWord_8156757).sum := by decide
  have hdescent : baseEnd_8156757 < baseStart_8156757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156827 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_8156827 : Nat := 118140960795 + 8156827 * 2 ^ 59
def prefixEnd_8156827 : Nat := 4983230072969 + 3 ^ 40 * 8156827 * 2
def baseEnd_8156827 : Nat := 4188372866571463110549941

theorem tailTrace_8156827 : CollatzResearch.WordTrace tailWord_8156827 prefixEnd_8156827 4188372866571463110549941 := by
  unfold tailWord_8156827
  simp only [CollatzResearch.WordTrace]
  refine ⟨297503921620216328988332735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198335947746810885992221823 297503921620216328988332735)
  ·
    refine ⟨446255882430324493482499103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297503921620216328988332735 446255882430324493482499103)
    ·
      refine ⟨669383823645486740223748655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446255882430324493482499103 669383823645486740223748655)
      ·
        refine ⟨1004075735468230110335622983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669383823645486740223748655 1004075735468230110335622983)
        ·
          refine ⟨1506113603202345165503434475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004075735468230110335622983 1506113603202345165503434475)
          ·
            refine ⟨2259170404803517748255151713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506113603202345165503434475 2259170404803517748255151713)
            ·
              refine ⟨1694377803602638311191363785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259170404803517748255151713 1694377803602638311191363785)
              ·
                refine ⟨1270783352701978733393522839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694377803602638311191363785 1270783352701978733393522839)
                ·
                  refine ⟨1906175029052968100090284259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270783352701978733393522839 1906175029052968100090284259)
                  ·
                    refine ⟨2859262543579452150135426389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1906175029052968100090284259 2859262543579452150135426389)
                    ·
                      refine ⟨4188372866571463110549941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2859262543579452150135426389 4188372866571463110549941)
                      ·
                        rfl

theorem cell23_8156827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_8156827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156827 prefixEnd_8156827 := by exact prefixLift 8156827
  have htrace : WordTrace (prefixWord ++ tailWord_8156827) baseStart_8156827 baseEnd_8156827 := by
    simpa [prefixWord, tailWord_8156827, baseEnd_8156827] using wordTrace_append hprefix tailTrace_8156827
  have hstable : (prefixWord ++ tailWord_8156827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156827).length < 2 ^ (prefixWord ++ tailWord_8156827).sum := by decide
  have hdescent : baseEnd_8156827 < baseStart_8156827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156881 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 6]
def baseStart_8156881 : Nat := 118140960795 + 8156881 * 2 ^ 59
def prefixEnd_8156881 : Nat := 4983230072969 + 3 ^ 40 * 8156881 * 2
def baseEnd_8156881 : Nat := 465377843836311766586077

theorem tailTrace_8156881 : CollatzResearch.WordTrace tailWord_8156881 prefixEnd_8156881 465377843836311766586077 := by
  unfold tailWord_8156881
  simp only [CollatzResearch.WordTrace]
  refine ⟨297505891162020696210798497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198337260774680464140532331 297505891162020696210798497)
  ·
    refine ⟨223129418371515522158098873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297505891162020696210798497 223129418371515522158098873)
    ·
      refine ⟨167347063778636641618574155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223129418371515522158098873 167347063778636641618574155)
      ·
        refine ⟨251020595667954962427861233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167347063778636641618574155 251020595667954962427861233)
        ·
          refine ⟨188265446750966221820895925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251020595667954962427861233 188265446750966221820895925)
          ·
            refine ⟨17649885632903083295708993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188265446750966221820895925 17649885632903083295708993)
            ·
              refine ⟨13237414224677312471781745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17649885632903083295708993 13237414224677312471781745)
              ·
                refine ⟨9928060668507984353836309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13237414224677312471781745 9928060668507984353836309)
                ·
                  refine ⟨465377843836311766586077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9928060668507984353836309 465377843836311766586077)
                  ·
                    rfl

theorem cell23_8156881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 6].length) (baseStart_8156881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156881 prefixEnd_8156881 := by exact prefixLift 8156881
  have htrace : WordTrace (prefixWord ++ tailWord_8156881) baseStart_8156881 baseEnd_8156881 := by
    simpa [prefixWord, tailWord_8156881, baseEnd_8156881] using wordTrace_append hprefix tailTrace_8156881
  have hstable : (prefixWord ++ tailWord_8156881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156881).length < 2 ^ (prefixWord ++ tailWord_8156881).sum := by decide
  have hdescent : baseEnd_8156881 < baseStart_8156881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156911 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 1, 5]
def baseStart_8156911 : Nat := 118140960795 + 8156911 * 2 ^ 59
def prefixEnd_8156911 : Nat := 4983230072969 + 3 ^ 40 * 8156911 * 2
def baseEnd_8156911 : Nat := 1396138666315480260633185

theorem tailTrace_8156911 : CollatzResearch.WordTrace tailWord_8156911 prefixEnd_8156911 1396138666315480260633185 := by
  unfold tailWord_8156911
  simp only [CollatzResearch.WordTrace]
  refine ⟨297506985351912011334390587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198337990234608007556260391 297506985351912011334390587)
  ·
    refine ⟨446260478027868017001585881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297506985351912011334390587 446260478027868017001585881)
    ·
      refine ⟨334695358520901012751189411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446260478027868017001585881 334695358520901012751189411)
      ·
        refine ⟨502043037781351519126784117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334695358520901012751189411 502043037781351519126784117)
        ·
          refine ⟨47066534792001704918136011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502043037781351519126784117 47066534792001704918136011)
          ·
            refine ⟨70599802188002557377204017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47066534792001704918136011 70599802188002557377204017)
            ·
              refine ⟨52949851641001918032903013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70599802188002557377204017 52949851641001918032903013)
              ·
                refine ⟨9928097182687859631169315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52949851641001918032903013 9928097182687859631169315)
                ·
                  refine ⟨14892145774031789446753973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928097182687859631169315 14892145774031789446753973)
                  ·
                    refine ⟨1396138666315480260633185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14892145774031789446753973 1396138666315480260633185)
                    ·
                      rfl

theorem cell23_8156911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_8156911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156911 prefixEnd_8156911 := by exact prefixLift 8156911
  have htrace : WordTrace (prefixWord ++ tailWord_8156911) baseStart_8156911 baseEnd_8156911 := by
    simpa [prefixWord, tailWord_8156911, baseEnd_8156911] using wordTrace_append hprefix tailTrace_8156911
  have hstable : (prefixWord ++ tailWord_8156911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156911).length < 2 ^ (prefixWord ++ tailWord_8156911).sum := by decide
  have hdescent : baseEnd_8156911 < baseStart_8156911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156951 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_8156951 : Nat := 118140960795 + 8156951 * 2 ^ 59
def prefixEnd_8156951 : Nat := 4983230072969 + 3 ^ 40 * 8156951 * 2
def baseEnd_8156951 : Nat := 4188436538172620625399371

theorem tailTrace_8156951 : CollatzResearch.WordTrace tailWord_8156951 prefixEnd_8156951 4188436538172620625399371 := by
  unfold tailWord_8156951
  simp only [CollatzResearch.WordTrace]
  refine ⟨297508444271767098165846707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198338962847844732110564471 297508444271767098165846707)
  ·
    refine ⟨446262666407650647248770061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297508444271767098165846707 446262666407650647248770061)
    ·
      refine ⟨167348499902868992718288773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446262666407650647248770061 167348499902868992718288773)
      ·
        refine ⟨31377843731787936134679145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167348499902868992718288773 31377843731787936134679145)
        ·
          refine ⟨23533382798840952101009359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31377843731787936134679145 23533382798840952101009359)
          ·
            refine ⟨35300074198261428151514039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23533382798840952101009359 35300074198261428151514039)
            ·
              refine ⟨52950111297392142227271059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35300074198261428151514039 52950111297392142227271059)
              ·
                refine ⟨79425166946088213340906589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52950111297392142227271059 79425166946088213340906589)
                ·
                  refine ⟨29784437604783080002839971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79425166946088213340906589 29784437604783080002839971)
                  ·
                    refine ⟨44676656407174620004259957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29784437604783080002839971 44676656407174620004259957)
                    ·
                      refine ⟨4188436538172620625399371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44676656407174620004259957 4188436538172620625399371)
                      ·
                        rfl

theorem cell23_8156951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_8156951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156951 prefixEnd_8156951 := by exact prefixLift 8156951
  have htrace : WordTrace (prefixWord ++ tailWord_8156951) baseStart_8156951 baseEnd_8156951 := by
    simpa [prefixWord, tailWord_8156951, baseEnd_8156951] using wordTrace_append hprefix tailTrace_8156951
  have hstable : (prefixWord ++ tailWord_8156951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156951).length < 2 ^ (prefixWord ++ tailWord_8156951).sum := by decide
  have hdescent : baseEnd_8156951 < baseStart_8156951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156961 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_8156961 : Nat := 118140960795 + 8156961 * 2 ^ 59
def prefixEnd_8156961 : Nat := 4983230072969 + 3 ^ 40 * 8156961 * 2
def baseEnd_8156961 : Nat := 4188441672979165586274325

theorem tailTrace_8156961 : CollatzResearch.WordTrace tailWord_8156961 prefixEnd_8156961 4188441672979165586274325 := by
  unfold tailWord_8156961
  simp only [CollatzResearch.WordTrace]
  refine ⟨297508809001730869873710737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198339206001153913249140491 297508809001730869873710737)
  ·
    refine ⟨223131606751298152405283053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297508809001730869873710737 223131606751298152405283053)
    ·
      refine ⟨83674352531736807151981145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223131606751298152405283053 83674352531736807151981145)
      ·
        refine ⟨62755764398802605363985859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83674352531736807151981145 62755764398802605363985859)
        ·
          refine ⟨94133646598203908045978789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62755764398802605363985859 94133646598203908045978789)
          ·
            refine ⟨17650058737163232758621023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94133646598203908045978789 17650058737163232758621023)
            ·
              refine ⟨26475088105744849137931535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17650058737163232758621023 26475088105744849137931535)
              ·
                refine ⟨39712632158617273706897303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26475088105744849137931535 39712632158617273706897303)
                ·
                  refine ⟨59568948237925910560345955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39712632158617273706897303 59568948237925910560345955)
                  ·
                    refine ⟨89353422356888865840518933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59568948237925910560345955 89353422356888865840518933)
                    ·
                      refine ⟨4188441672979165586274325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89353422356888865840518933 4188441672979165586274325)
                      ·
                        rfl

theorem cell23_8156961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_8156961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156961 prefixEnd_8156961 := by exact prefixLift 8156961
  have htrace : WordTrace (prefixWord ++ tailWord_8156961) baseStart_8156961 baseEnd_8156961 := by
    simpa [prefixWord, tailWord_8156961, baseEnd_8156961] using wordTrace_append hprefix tailTrace_8156961
  have hstable : (prefixWord ++ tailWord_8156961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156961).length < 2 ^ (prefixWord ++ tailWord_8156961).sum := by decide
  have hdescent : baseEnd_8156961 < baseStart_8156961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156965 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 3, 2, 2]
def baseStart_8156965 : Nat := 118140960795 + 8156965 * 2 ^ 59
def prefixEnd_8156965 : Nat := 4983230072969 + 3 ^ 40 * 8156965 * 2
def baseEnd_8156965 : Nat := 4188443726901783570624307

theorem tailTrace_8156965 : CollatzResearch.WordTrace tailWord_8156965 prefixEnd_8156965 4188443726901783570624307 := by
  unfold tailWord_8156965
  simp only [CollatzResearch.WordTrace]
  refine ⟨297508954893716378556856349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198339303262477585704570899 297508954893716378556856349)
  ·
    refine ⟨111565858085143641958821131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297508954893716378556856349 111565858085143641958821131)
    ·
      refine ⟨167348787127715462938231697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111565858085143641958821131 167348787127715462938231697)
      ·
        refine ⟨125511590345786597203673773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167348787127715462938231697 125511590345786597203673773)
        ·
          refine ⟨47066846379669973951377665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125511590345786597203673773 47066846379669973951377665)
          ·
            refine ⟨35300134784752480463533249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47066846379669973951377665 35300134784752480463533249)
            ·
              refine ⟨26475101088564360347649937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35300134784752480463533249 26475101088564360347649937)
              ·
                refine ⟨19856325816423270260737453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26475101088564360347649937 19856325816423270260737453)
                ·
                  refine ⟨7446122181158726347776545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19856325816423270260737453 7446122181158726347776545)
                  ·
                    refine ⟨5584591635869044760832409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7446122181158726347776545 5584591635869044760832409)
                    ·
                      refine ⟨4188443726901783570624307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584591635869044760832409 4188443726901783570624307)
                      ·
                        rfl

theorem cell23_8156965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_8156965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156965 prefixEnd_8156965 := by exact prefixLift 8156965
  have htrace : WordTrace (prefixWord ++ tailWord_8156965) baseStart_8156965 baseEnd_8156965 := by
    simpa [prefixWord, tailWord_8156965, baseEnd_8156965] using wordTrace_append hprefix tailTrace_8156965
  have hstable : (prefixWord ++ tailWord_8156965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156965).length < 2 ^ (prefixWord ++ tailWord_8156965).sum := by decide
  have hdescent : baseEnd_8156965 < baseStart_8156965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8156985 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 5]
def baseStart_8156985 : Nat := 118140960795 + 8156985 * 2 ^ 59
def prefixEnd_8156985 : Nat := 4983230072969 + 3 ^ 40 * 8156985 * 2
def baseEnd_8156985 : Nat := 4188453996514873492374215

theorem tailTrace_8156985 : CollatzResearch.WordTrace tailWord_8156985 prefixEnd_8156985 4188453996514873492374215 := by
  unfold tailWord_8156985
  simp only [CollatzResearch.WordTrace]
  refine ⟨297509684353643921972584409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198339789569095947981722939 297509684353643921972584409)
  ·
    refine ⟨223132263265232941479438307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297509684353643921972584409 223132263265232941479438307)
    ·
      refine ⟨334698394897849412219157461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223132263265232941479438307 334698394897849412219157461)
      ·
        refine ⟨7844493630418345598886503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 334698394897849412219157461 7844493630418345598886503)
        ·
          refine ⟨11766740445627518398329755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7844493630418345598886503 11766740445627518398329755)
          ·
            refine ⟨17650110668441277597494633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766740445627518398329755 17650110668441277597494633)
            ·
              refine ⟨13237583001330958198120975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17650110668441277597494633 13237583001330958198120975)
              ·
                refine ⟨19856374501996437297181463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13237583001330958198120975 19856374501996437297181463)
                ·
                  refine ⟨29784561752994655945772195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19856374501996437297181463 29784561752994655945772195)
                  ·
                    refine ⟨44676842629491983918658293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29784561752994655945772195 44676842629491983918658293)
                    ·
                      refine ⟨4188453996514873492374215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44676842629491983918658293 4188453996514873492374215)
                      ·
                        rfl

theorem cell23_8156985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_8156985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8156985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8156985 prefixEnd_8156985 := by exact prefixLift 8156985
  have htrace : WordTrace (prefixWord ++ tailWord_8156985) baseStart_8156985 baseEnd_8156985 := by
    simpa [prefixWord, tailWord_8156985, baseEnd_8156985] using wordTrace_append hprefix tailTrace_8156985
  have hstable : (prefixWord ++ tailWord_8156985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8156985).length < 2 ^ (prefixWord ++ tailWord_8156985).sum := by decide
  have hdescent : baseEnd_8156985 < baseStart_8156985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8156985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157008 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 3, 3, 2]
def baseStart_8157008 : Nat := 118140960795 + 8157008 * 2 ^ 59
def prefixEnd_8157008 : Nat := 4983230072969 + 3 ^ 40 * 8157008 * 2
def baseEnd_8157008 : Nat := 4188465806569926902386609

theorem tailTrace_8157008 : CollatzResearch.WordTrace tailWord_8157008 prefixEnd_8157008 4188465806569926902386609 := by
  unfold tailWord_8157008
  simp only [CollatzResearch.WordTrace]
  refine ⟨148755261616280298450335839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198340348821707064600447785 148755261616280298450335839)
  ·
    refine ⟨223132892424420447675503759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148755261616280298450335839 223132892424420447675503759)
    ·
      refine ⟨334699338636630671513255639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223132892424420447675503759 334699338636630671513255639)
      ·
        refine ⟨502049007954946007269883459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334699338636630671513255639 502049007954946007269883459)
        ·
          refine ⟨753073511932419010904825189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502049007954946007269883459 753073511932419010904825189)
          ·
            refine ⟨141201283487328564544654723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 753073511932419010904825189 141201283487328564544654723)
            ·
              refine ⟨211801925230992846816982085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141201283487328564544654723 211801925230992846816982085)
              ·
                refine ⟨39712860980811158778184141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211801925230992846816982085 39712860980811158778184141)
                ·
                  refine ⟨14892322867804184541819053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39712860980811158778184141 14892322867804184541819053)
                  ·
                    refine ⟨5584621075426569203182145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14892322867804184541819053 5584621075426569203182145)
                    ·
                      refine ⟨4188465806569926902386609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584621075426569203182145 4188465806569926902386609)
                      ·
                        rfl

theorem cell23_8157008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 3, 2].length) (baseStart_8157008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157008 prefixEnd_8157008 := by exact prefixLift 8157008
  have htrace : WordTrace (prefixWord ++ tailWord_8157008) baseStart_8157008 baseEnd_8157008 := by
    simpa [prefixWord, tailWord_8157008, baseEnd_8157008] using wordTrace_append hprefix tailTrace_8157008
  have hstable : (prefixWord ++ tailWord_8157008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157008).length < 2 ^ (prefixWord ++ tailWord_8157008).sum := by decide
  have hdescent : baseEnd_8157008 < baseStart_8157008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157041 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_8157041 : Nat := 118140960795 + 8157041 * 2 ^ 59
def prefixEnd_8157041 : Nat := 4983230072969 + 3 ^ 40 * 8157041 * 2
def baseEnd_8157041 : Nat := 4188482751431525273273957

theorem tailTrace_8157041 : CollatzResearch.WordTrace tailWord_8157041 prefixEnd_8157041 4188482751431525273273957 := by
  unfold tailWord_8157041
  simp only [CollatzResearch.WordTrace]
  refine ⟨297511726841441043536622977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198341151227627362357748651 297511726841441043536622977)
  ·
    refine ⟨223133795131080782652467233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297511726841441043536622977 223133795131080782652467233)
    ·
      refine ⟨167350346348310586989350425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223133795131080782652467233 167350346348310586989350425)
      ·
        refine ⟨125512759761232940242012819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167350346348310586989350425 125512759761232940242012819)
        ·
          refine ⟨188269139641849410363019229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125512759761232940242012819 188269139641849410363019229)
          ·
            refine ⟨70600927365693528886132211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188269139641849410363019229 70600927365693528886132211)
            ·
              refine ⟨105901391048540293329198317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70600927365693528886132211 105901391048540293329198317)
              ·
                refine ⟨39713021643202609998449369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105901391048540293329198317 39713021643202609998449369)
                ·
                  refine ⟨29784766232401957498837027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39713021643202609998449369 29784766232401957498837027)
                  ·
                    refine ⟨44677149348602936248255541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29784766232401957498837027 44677149348602936248255541)
                    ·
                      refine ⟨4188482751431525273273957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44677149348602936248255541 4188482751431525273273957)
                      ·
                        rfl

theorem cell23_8157041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_8157041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157041 prefixEnd_8157041 := by exact prefixLift 8157041
  have htrace : WordTrace (prefixWord ++ tailWord_8157041) baseStart_8157041 baseEnd_8157041 := by
    simpa [prefixWord, tailWord_8157041, baseEnd_8157041] using wordTrace_append hprefix tailTrace_8157041
  have hstable : (prefixWord ++ tailWord_8157041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157041).length < 2 ^ (prefixWord ++ tailWord_8157041).sum := by decide
  have hdescent : baseEnd_8157041 < baseStart_8157041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157051 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4]
def baseStart_8157051 : Nat := 118140960795 + 8157051 * 2 ^ 59
def prefixEnd_8157051 : Nat := 4983230072969 + 3 ^ 40 * 8157051 * 2
def baseEnd_8157051 : Nat := 4188487886238070234148911

theorem tailTrace_8157051 : CollatzResearch.WordTrace tailWord_8157051 prefixEnd_8157051 4188487886238070234148911 := by
  unfold tailWord_8157051
  simp only [CollatzResearch.WordTrace]
  refine ⟨297512091571404815244487007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198341394380936543496324671 297512091571404815244487007)
  ·
    refine ⟨446268137357107222866730511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297512091571404815244487007 446268137357107222866730511)
    ·
      refine ⟨669402206035660834300095767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446268137357107222866730511 669402206035660834300095767)
      ·
        refine ⟨1004103309053491251450143651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669402206035660834300095767 1004103309053491251450143651)
        ·
          refine ⟨1506154963580236877175215477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004103309053491251450143651 1506154963580236877175215477)
          ·
            refine ⟨141202027835647207235176451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1506154963580236877175215477 141202027835647207235176451)
            ·
              refine ⟨211803041753470810852764677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141202027835647207235176451 211803041753470810852764677)
              ·
                refine ⟨39713070328775777034893377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211803041753470810852764677 39713070328775777034893377)
                ·
                  refine ⟨29784802746581832776170033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39713070328775777034893377 29784802746581832776170033)
                  ·
                    refine ⟨22338602059936374582127525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29784802746581832776170033 22338602059936374582127525)
                    ·
                      refine ⟨4188487886238070234148911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22338602059936374582127525 4188487886238070234148911)
                      ·
                        rfl

theorem cell23_8157051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_8157051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157051 prefixEnd_8157051 := by exact prefixLift 8157051
  have htrace : WordTrace (prefixWord ++ tailWord_8157051) baseStart_8157051 baseEnd_8157051 := by
    simpa [prefixWord, tailWord_8157051, baseEnd_8157051] using wordTrace_append hprefix tailTrace_8157051
  have hstable : (prefixWord ++ tailWord_8157051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157051).length < 2 ^ (prefixWord ++ tailWord_8157051).sum := by decide
  have hdescent : baseEnd_8157051 < baseStart_8157051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157061 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 7]
def baseStart_8157061 : Nat := 118140960795 + 8157061 * 2 ^ 59
def prefixEnd_8157061 : Nat := 4983230072969 + 3 ^ 40 * 8157061 * 2
def baseEnd_8157061 : Nat := 465388113449401688335985

theorem tailTrace_8157061 : CollatzResearch.WordTrace tailWord_8157061 prefixEnd_8157061 465388113449401688335985 := by
  unfold tailWord_8157061
  simp only [CollatzResearch.WordTrace]
  refine ⟨297512456301368586952351037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198341637534245724634900691 297512456301368586952351037)
  ·
    refine ⟨111567171113013220107131639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297512456301368586952351037 111567171113013220107131639)
    ·
      refine ⟨167350756669519830160697459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111567171113013220107131639 167350756669519830160697459)
      ·
        refine ⟨251026135004279745241046189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167350756669519830160697459 251026135004279745241046189)
        ·
          refine ⟨94134800626604904465392321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251026135004279745241046189 94134800626604904465392321)
          ·
            refine ⟨70601100469953678349044241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94134800626604904465392321 70601100469953678349044241)
            ·
              refine ⟨52950825352465258761783181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70601100469953678349044241 52950825352465258761783181)
              ·
                refine ⟨19856559507174472035668693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52950825352465258761783181 19856559507174472035668693)
                ·
                  refine ⟨465388113449401688335985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19856559507174472035668693 465388113449401688335985)
                  ·
                    rfl

theorem cell23_8157061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_8157061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157061 prefixEnd_8157061 := by exact prefixLift 8157061
  have htrace : WordTrace (prefixWord ++ tailWord_8157061) baseStart_8157061 baseEnd_8157061 := by
    simpa [prefixWord, tailWord_8157061, baseEnd_8157061] using wordTrace_append hprefix tailTrace_8157061
  have hstable : (prefixWord ++ tailWord_8157061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157061).length < 2 ^ (prefixWord ++ tailWord_8157061).sum := by decide
  have hdescent : baseEnd_8157061 < baseStart_8157061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157095 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 5]
def baseStart_8157095 : Nat := 118140960795 + 8157095 * 2 ^ 59
def prefixEnd_8157095 : Nat := 4983230072969 + 3 ^ 40 * 8157095 * 2
def baseEnd_8157095 : Nat := 465390053265207562444301

theorem tailTrace_8157095 : CollatzResearch.WordTrace tailWord_8157095 prefixEnd_8157095 465390053265207562444301 := by
  unfold tailWord_8157095
  simp only [CollatzResearch.WordTrace]
  refine ⟨297513696383245410759088739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198342464255496940506059159 297513696383245410759088739)
  ·
    refine ⟨446270544574868116138633109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297513696383245410759088739 446270544574868116138633109)
    ·
      refine ⟨20918931776946942943998427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 446270544574868116138633109 20918931776946942943998427)
      ·
        refine ⟨31378397665420414415997641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20918931776946942943998427 31378397665420414415997641)
        ·
          refine ⟨23533798249065310811998231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31378397665420414415997641 23533798249065310811998231)
          ·
            refine ⟨35300697373597966217997347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23533798249065310811998231 35300697373597966217997347)
            ·
              refine ⟨52951046060396949326996021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35300697373597966217997347 52951046060396949326996021)
              ·
                refine ⟨4964160568162213999405877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52951046060396949326996021 4964160568162213999405877)
                ·
                  refine ⟨465390053265207562444301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4964160568162213999405877 465390053265207562444301)
                  ·
                    rfl

theorem cell23_8157095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 5].length) (baseStart_8157095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157095 prefixEnd_8157095 := by exact prefixLift 8157095
  have htrace : WordTrace (prefixWord ++ tailWord_8157095) baseStart_8157095 baseEnd_8157095 := by
    simpa [prefixWord, tailWord_8157095, baseEnd_8157095] using wordTrace_append hprefix tailTrace_8157095
  have hstable : (prefixWord ++ tailWord_8157095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157095).length < 2 ^ (prefixWord ++ tailWord_8157095).sum := by decide
  have hdescent : baseEnd_8157095 < baseStart_8157095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157128 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_8157128 : Nat := 118140960795 + 8157128 * 2 ^ 59
def prefixEnd_8157128 : Nat := 4983230072969 + 3 ^ 40 * 8157128 * 2
def baseEnd_8157128 : Nat := 4188527424248466432886057

theorem tailTrace_8157128 : CollatzResearch.WordTrace tailWord_8157128 prefixEnd_8157128 4188527424248466432886057 := by
  unfold tailWord_8157128
  simp only [CollatzResearch.WordTrace]
  refine ⟨148757449996062928697520019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198343266661417238263360025 148757449996062928697520019)
  ·
    refine ⟨223136174994094393046280029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148757449996062928697520019 223136174994094393046280029)
    ·
      refine ⟨83676065622785397392355011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223136174994094393046280029 83676065622785397392355011)
      ·
        refine ⟨125514098434178096088532517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83676065622785397392355011 125514098434178096088532517)
        ·
          refine ⟨23533893456408393016599847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125514098434178096088532517 23533893456408393016599847)
          ·
            refine ⟨35300840184612589524899771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23533893456408393016599847 35300840184612589524899771)
            ·
              refine ⟨52951260276918884287349657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35300840184612589524899771 52951260276918884287349657)
              ·
                refine ⟨39713445207689163215512243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52951260276918884287349657 39713445207689163215512243)
                ·
                  refine ⟨59570167811533744823268365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39713445207689163215512243 59570167811533744823268365)
                  ·
                    refine ⟨22338812929325154308725637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59570167811533744823268365 22338812929325154308725637)
                    ·
                      refine ⟨4188527424248466432886057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22338812929325154308725637 4188527424248466432886057)
                      ·
                        rfl

theorem cell23_8157128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_8157128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157128 prefixEnd_8157128 := by exact prefixLift 8157128
  have htrace : WordTrace (prefixWord ++ tailWord_8157128) baseStart_8157128 baseEnd_8157128 := by
    simpa [prefixWord, tailWord_8157128, baseEnd_8157128] using wordTrace_append hprefix tailTrace_8157128
  have hstable : (prefixWord ++ tailWord_8157128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157128).length < 2 ^ (prefixWord ++ tailWord_8157128).sum := by decide
  have hdescent : baseEnd_8157128 < baseStart_8157128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157171 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_8157171 : Nat := 118140960795 + 8157171 * 2 ^ 59
def prefixEnd_8157171 : Nat := 4983230072969 + 3 ^ 40 * 8157171 * 2
def baseEnd_8157171 : Nat := 4188549503916609764648359

theorem tailTrace_8157171 : CollatzResearch.WordTrace tailWord_8157171 prefixEnd_8157171 4188549503916609764648359 := by
  unfold tailWord_8157171
  simp only [CollatzResearch.WordTrace]
  refine ⟨297516468330970075738855367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198344312220646717159236911 297516468330970075738855367)
  ·
    refine ⟨446274702496455113608283051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297516468330970075738855367 446274702496455113608283051)
    ·
      refine ⟨669412053744682670412424577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446274702496455113608283051 669412053744682670412424577)
      ·
        refine ⟨502059040308512002809318433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669412053744682670412424577 502059040308512002809318433)
        ·
          refine ⟨376544280231384002106988825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502059040308512002809318433 376544280231384002106988825)
          ·
            refine ⟨282408210173538001580241619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376544280231384002106988825 282408210173538001580241619)
            ·
              refine ⟨423612315260307002370362429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282408210173538001580241619 423612315260307002370362429)
              ·
                refine ⟨158854618222615125888885911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423612315260307002370362429 158854618222615125888885911)
                ·
                  refine ⟨238281927333922688833328867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158854618222615125888885911 238281927333922688833328867)
                  ·
                    refine ⟨357422891000884033249993301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238281927333922688833328867 357422891000884033249993301)
                    ·
                      refine ⟨4188549503916609764648359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357422891000884033249993301 4188549503916609764648359)
                      ·
                        rfl

theorem cell23_8157171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_8157171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157171 prefixEnd_8157171 := by exact prefixLift 8157171
  have htrace : WordTrace (prefixWord ++ tailWord_8157171) baseStart_8157171 baseEnd_8157171 := by
    simpa [prefixWord, tailWord_8157171, baseEnd_8157171] using wordTrace_append hprefix tailTrace_8157171
  have hstable : (prefixWord ++ tailWord_8157171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157171).length < 2 ^ (prefixWord ++ tailWord_8157171).sum := by decide
  have hdescent : baseEnd_8157171 < baseStart_8157171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157195 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 3]
def baseStart_8157195 : Nat := 118140960795 + 8157195 * 2 ^ 59
def prefixEnd_8157195 : Nat := 4983230072969 + 3 ^ 40 * 8157195 * 2
def baseEnd_8157195 : Nat := 4188561827452317670748249

theorem tailTrace_8157195 : CollatzResearch.WordTrace tailWord_8157195 prefixEnd_8157195 4188561827452317670748249 := by
  unfold tailWord_8157195
  simp only [CollatzResearch.WordTrace]
  refine ⟨297517343682883127837729039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198344895788588751891819359 297517343682883127837729039)
  ·
    refine ⟨446276015524324691756593559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297517343682883127837729039 446276015524324691756593559)
    ·
      refine ⟨669414023286487037634890339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446276015524324691756593559 669414023286487037634890339)
      ·
        refine ⟨1004121034929730556452335509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669414023286487037634890339 1004121034929730556452335509)
        ·
          refine ⟨47068173512331119833703227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1004121034929730556452335509 47068173512331119833703227)
          ·
            refine ⟨70602260268496679750554841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47068173512331119833703227 70602260268496679750554841)
            ·
              refine ⟨52951695201372509812916131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70602260268496679750554841 52951695201372509812916131)
              ·
                refine ⟨79427542802058764719374197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52951695201372509812916131 79427542802058764719374197)
                ·
                  refine ⟨7446332137693009192441331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79427542802058764719374197 7446332137693009192441331)
                  ·
                    refine ⟨11169498206539513788661997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7446332137693009192441331 11169498206539513788661997)
                    ·
                      refine ⟨4188561827452317670748249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11169498206539513788661997 4188561827452317670748249)
                      ·
                        rfl

theorem cell23_8157195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 3].length) (baseStart_8157195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157195 prefixEnd_8157195 := by exact prefixLift 8157195
  have htrace : WordTrace (prefixWord ++ tailWord_8157195) baseStart_8157195 baseEnd_8157195 := by
    simpa [prefixWord, tailWord_8157195, baseEnd_8157195] using wordTrace_append hprefix tailTrace_8157195
  have hstable : (prefixWord ++ tailWord_8157195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157195).length < 2 ^ (prefixWord ++ tailWord_8157195).sum := by decide
  have hdescent : baseEnd_8157195 < baseStart_8157195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157223 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 1, 4]
def baseStart_8157223 : Nat := 118140960795 + 8157223 * 2 ^ 59
def prefixEnd_8157223 : Nat := 4983230072969 + 3 ^ 40 * 8157223 * 2
def baseEnd_8157223 : Nat := 1396192068303547853732707

theorem tailTrace_8157223 : CollatzResearch.WordTrace tailWord_8157223 prefixEnd_8157223 1396192068303547853732707 := by
  unfold tailWord_8157223
  simp only [CollatzResearch.WordTrace]
  refine ⟨297518364926781688619748323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198345576617854459079832215 297518364926781688619748323)
  ·
    refine ⟨446277547390172532929622485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297518364926781688619748323 446277547390172532929622485)
    ·
      refine ⟨10459630016957168740538027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 446277547390172532929622485 10459630016957168740538027)
      ·
        refine ⟨15689445025435753110807041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10459630016957168740538027 15689445025435753110807041)
        ·
          refine ⟨11767083769076814833105281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15689445025435753110807041 11767083769076814833105281)
          ·
            refine ⟨8825312826807611124828961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11767083769076814833105281 8825312826807611124828961)
            ·
              refine ⟨6618984620105708343621721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8825312826807611124828961 6618984620105708343621721)
              ·
                refine ⟨4964238465079281257716291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6618984620105708343621721 4964238465079281257716291)
                ·
                  refine ⟨7446357697618921886574437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964238465079281257716291 7446357697618921886574437)
                  ·
                    refine ⟨1396192068303547853732707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7446357697618921886574437 1396192068303547853732707)
                    ·
                      rfl

theorem cell23_8157223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_8157223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157223 prefixEnd_8157223 := by exact prefixLift 8157223
  have htrace : WordTrace (prefixWord ++ tailWord_8157223) baseStart_8157223 baseEnd_8157223 := by
    simpa [prefixWord, tailWord_8157223, baseEnd_8157223] using wordTrace_append hprefix tailTrace_8157223
  have hstable : (prefixWord ++ tailWord_8157223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157223).length < 2 ^ (prefixWord ++ tailWord_8157223).sum := by decide
  have hdescent : baseEnd_8157223 < baseStart_8157223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157245 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_8157245 : Nat := 118140960795 + 8157245 * 2 ^ 59
def prefixEnd_8157245 : Nat := 4983230072969 + 3 ^ 40 * 8157245 * 2
def baseEnd_8157245 : Nat := 1396195833828347491707673

theorem tailTrace_8157245 : CollatzResearch.WordTrace tailWord_8157245 prefixEnd_8157245 1396195833828347491707673 := by
  unfold tailWord_8157245
  simp only [CollatzResearch.WordTrace]
  refine ⟨297519167332701986377049189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198346111555134657584699459 297519167332701986377049189)
  ·
    refine ⟨55784843874881622445696723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297519167332701986377049189 55784843874881622445696723)
    ·
      refine ⟨83677265812322433668545085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55784843874881622445696723 83677265812322433668545085)
      ·
        refine ⟨31378974679620912625704407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83677265812322433668545085 31378974679620912625704407)
        ·
          refine ⟨47068462019431368938556611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31378974679620912625704407 47068462019431368938556611)
          ·
            refine ⟨70602693029147053407834917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47068462019431368938556611 70602693029147053407834917)
            ·
              refine ⟨13238004942965072513969047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70602693029147053407834917 13238004942965072513969047)
              ·
                refine ⟨19857007414447608770953571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13238004942965072513969047 19857007414447608770953571)
                ·
                  refine ⟨29785511121671413156430357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19857007414447608770953571 29785511121671413156430357)
                  ·
                    refine ⟨1396195833828347491707673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29785511121671413156430357 1396195833828347491707673)
                    ·
                      rfl

theorem cell23_8157245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_8157245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157245 prefixEnd_8157245 := by exact prefixLift 8157245
  have htrace : WordTrace (prefixWord ++ tailWord_8157245) baseStart_8157245 baseEnd_8157245 := by
    simpa [prefixWord, tailWord_8157245, baseEnd_8157245] using wordTrace_append hprefix tailTrace_8157245
  have hstable : (prefixWord ++ tailWord_8157245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157245).length < 2 ^ (prefixWord ++ tailWord_8157245).sum := by decide
  have hdescent : baseEnd_8157245 < baseStart_8157245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157255 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_8157255 : Nat := 118140960795 + 8157255 * 2 ^ 59
def prefixEnd_8157255 : Nat := 4983230072969 + 3 ^ 40 * 8157255 * 2
def baseEnd_8157255 : Nat := 4188592636291587435997973

theorem tailTrace_8157255 : CollatzResearch.WordTrace tailWord_8157255 prefixEnd_8157255 4188592636291587435997973 := by
  unfold tailWord_8157255
  simp only [CollatzResearch.WordTrace]
  refine ⟨297519532062665758084913219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198346354708443838723275479 297519532062665758084913219)
  ·
    refine ⟨446279298093998637127369829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297519532062665758084913219 446279298093998637127369829)
    ·
      refine ⟨83677368392624744461381843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446279298093998637127369829 83677368392624744461381843)
      ·
        refine ⟨125516052588937116692072765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83677368392624744461381843 125516052588937116692072765)
        ·
          refine ⟨47068519720851418759527287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125516052588937116692072765 47068519720851418759527287)
          ·
            refine ⟨70602779581277128139290931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47068519720851418759527287 70602779581277128139290931)
            ·
              refine ⟨105904169371915692208936397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70602779581277128139290931 105904169371915692208936397)
              ·
                refine ⟨39714063514468384578351149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105904169371915692208936397 39714063514468384578351149)
                ·
                  refine ⟨14892773817925644216881681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39714063514468384578351149 14892773817925644216881681)
                  ·
                    refine ⟨11169580363444233162661261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14892773817925644216881681 11169580363444233162661261)
                    ·
                      refine ⟨4188592636291587435997973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11169580363444233162661261 4188592636291587435997973)
                      ·
                        rfl

theorem cell23_8157255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_8157255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157255 prefixEnd_8157255 := by exact prefixLift 8157255
  have htrace : WordTrace (prefixWord ++ tailWord_8157255) baseStart_8157255 baseEnd_8157255 := by
    simpa [prefixWord, tailWord_8157255, baseEnd_8157255] using wordTrace_append hprefix tailTrace_8157255
  have hstable : (prefixWord ++ tailWord_8157255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157255).length < 2 ^ (prefixWord ++ tailWord_8157255).sum := by decide
  have hdescent : baseEnd_8157255 < baseStart_8157255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157266 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_8157266 : Nat := 118140960795 + 8157266 * 2 ^ 59
def prefixEnd_8157266 : Nat := 4983230072969 + 3 ^ 40 * 8157266 * 2
def baseEnd_8157266 : Nat := 1396199428192928964320141

theorem tailTrace_8157266 : CollatzResearch.WordTrace tailWord_8157266 prefixEnd_8157266 1396199428192928964320141 := by
  unfold tailWord_8157266
  simp only [CollatzResearch.WordTrace]
  refine ⟨74379983316406476740890913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198346622177083937975709101 74379983316406476740890913)
  ·
    refine ⟨55784987487304857555668185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74379983316406476740890913 55784987487304857555668185)
    ·
      refine ⟨41838740615478643166751139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55784987487304857555668185 41838740615478643166751139)
      ·
        refine ⟨62758110923217964750126709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41838740615478643166751139 62758110923217964750126709)
        ·
          refine ⟨5883572899051684195324379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62758110923217964750126709 5883572899051684195324379)
          ·
            refine ⟨8825359348577526292986569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883572899051684195324379 8825359348577526292986569)
            ·
              refine ⟨6619019511433144719739927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8825359348577526292986569 6619019511433144719739927)
              ·
                refine ⟨9928529267149717079609891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619019511433144719739927 9928529267149717079609891)
                ·
                  refine ⟨14892793900724575619414837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928529267149717079609891 14892793900724575619414837)
                  ·
                    refine ⟨1396199428192928964320141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14892793900724575619414837 1396199428192928964320141)
                    ·
                      rfl

theorem cell23_8157266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_8157266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157266 prefixEnd_8157266 := by exact prefixLift 8157266
  have htrace : WordTrace (prefixWord ++ tailWord_8157266) baseStart_8157266 baseEnd_8157266 := by
    simpa [prefixWord, tailWord_8157266, baseEnd_8157266] using wordTrace_append hprefix tailTrace_8157266
  have hstable : (prefixWord ++ tailWord_8157266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157266).length < 2 ^ (prefixWord ++ tailWord_8157266).sum := by decide
  have hdescent : baseEnd_8157266 < baseStart_8157266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157269 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_8157269 : Nat := 118140960795 + 8157269 * 2 ^ 59
def prefixEnd_8157269 : Nat := 4983230072969 + 3 ^ 40 * 8157269 * 2
def baseEnd_8157269 : Nat := 4188599825020750381222909

theorem tailTrace_8157269 : CollatzResearch.WordTrace tailWord_8157269 prefixEnd_8157269 4188599825020750381222909 := by
  unfold tailWord_8157269
  simp only [CollatzResearch.WordTrace]
  refine ⟨297520042684615038475922861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198346695123076692317281907 297520042684615038475922861)
  ·
    refine ⟨111570016006730639428471073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297520042684615038475922861 111570016006730639428471073)
    ·
      refine ⟨83677512005047979571353305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111570016006730639428471073 83677512005047979571353305)
      ·
        refine ⟨62758134003785984678514979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83677512005047979571353305 62758134003785984678514979)
        ·
          refine ⟨94137201005678977017772469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62758134003785984678514979 94137201005678977017772469)
          ·
            refine ⟨8825362594282404095416169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94137201005678977017772469 8825362594282404095416169)
            ·
              refine ⟨6619021945711803071562127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8825362594282404095416169 6619021945711803071562127)
              ·
                refine ⟨9928532918567704607343191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619021945711803071562127 9928532918567704607343191)
                ·
                  refine ⟨14892799377851556911014787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928532918567704607343191 14892799377851556911014787)
                  ·
                    refine ⟨22339199066777335366522181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14892799377851556911014787 22339199066777335366522181)
                    ·
                      refine ⟨4188599825020750381222909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22339199066777335366522181 4188599825020750381222909)
                      ·
                        rfl

theorem cell23_8157269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_8157269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157269 prefixEnd_8157269 := by exact prefixLift 8157269
  have htrace : WordTrace (prefixWord ++ tailWord_8157269) baseStart_8157269 baseEnd_8157269 := by
    simpa [prefixWord, tailWord_8157269, baseEnd_8157269] using wordTrace_append hprefix tailTrace_8157269
  have hstable : (prefixWord ++ tailWord_8157269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157269).length < 2 ^ (prefixWord ++ tailWord_8157269).sum := by decide
  have hdescent : baseEnd_8157269 < baseStart_8157269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157272 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_8157272 : Nat := 118140960795 + 8157272 * 2 ^ 59
def prefixEnd_8157272 : Nat := 4983230072969 + 3 ^ 40 * 8157272 * 2
def baseEnd_8157272 : Nat := 4188601365462713869485395

theorem tailTrace_8157272 : CollatzResearch.WordTrace tailWord_8157272 prefixEnd_8157272 4188601365462713869485395 := by
  unfold tailWord_8157272
  simp only [CollatzResearch.WordTrace]
  refine ⟨148760076051802084994141035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198346768069069446658854713 148760076051802084994141035)
  ·
    refine ⟨223140114077703127491211553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148760076051802084994141035 223140114077703127491211553)
    ·
      refine ⟨167355085558277345618408665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223140114077703127491211553 167355085558277345618408665)
      ·
        refine ⟨125516314168708009213806499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167355085558277345618408665 125516314168708009213806499)
        ·
          refine ⟨188274471253062013820709749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125516314168708009213806499 188274471253062013820709749)
          ·
            refine ⟨17650731679974563795691539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188274471253062013820709749 17650731679974563795691539)
            ·
              refine ⟨26476097519961845693537309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17650731679974563795691539 26476097519961845693537309)
              ·
                refine ⟨9928536569985692135076491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26476097519961845693537309 9928536569985692135076491)
                ·
                  refine ⟨14892804854978538202614737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928536569985692135076491 14892804854978538202614737)
                  ·
                    refine ⟨11169603641233903651961053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14892804854978538202614737 11169603641233903651961053)
                    ·
                      refine ⟨4188601365462713869485395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11169603641233903651961053 4188601365462713869485395)
                      ·
                        rfl

theorem cell23_8157272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_8157272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157272 prefixEnd_8157272 := by exact prefixLift 8157272
  have htrace : WordTrace (prefixWord ++ tailWord_8157272) baseStart_8157272 baseEnd_8157272 := by
    simpa [prefixWord, tailWord_8157272, baseEnd_8157272] using wordTrace_append hprefix tailTrace_8157272
  have hstable : (prefixWord ++ tailWord_8157272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157272).length < 2 ^ (prefixWord ++ tailWord_8157272).sum := by decide
  have hdescent : baseEnd_8157272 < baseStart_8157272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157375 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_8157375 : Nat := 118140960795 + 8157375 * 2 ^ 59
def prefixEnd_8157375 : Nat := 4983230072969 + 3 ^ 40 * 8157375 * 2
def baseEnd_8157375 : Nat := 4188654253970126966497421

theorem tailTrace_8157375 : CollatzResearch.WordTrace tailWord_8157375 prefixEnd_8157375 4188654253970126966497421 := by
  unfold tailWord_8157375
  simp only [CollatzResearch.WordTrace]
  refine ⟨297523908822231018579281579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198349272548154012386187719 297523908822231018579281579)
  ·
    refine ⟨446285863233346527868922369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297523908822231018579281579 446285863233346527868922369)
    ·
      refine ⟨334714397425009895901691777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446285863233346527868922369 334714397425009895901691777)
      ·
        refine ⟨251035798068757421926268833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334714397425009895901691777 251035798068757421926268833)
        ·
          refine ⟨188276848551568066444701625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251035798068757421926268833 188276848551568066444701625)
          ·
            refine ⟨141207636413676049833526219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188276848551568066444701625 141207636413676049833526219)
            ·
              refine ⟨211811454620514074750289329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141207636413676049833526219 211811454620514074750289329)
              ·
                refine ⟨158858590965385556062716997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211811454620514074750289329 158858590965385556062716997)
                ·
                  refine ⟨29785985806009791761759437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158858590965385556062716997 29785985806009791761759437)
                  ·
                    refine ⟨11169744677253671910659789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29785985806009791761759437 11169744677253671910659789)
                    ·
                      refine ⟨4188654253970126966497421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11169744677253671910659789 4188654253970126966497421)
                      ·
                        rfl

theorem cell23_8157375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_8157375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157375 prefixEnd_8157375 := by exact prefixLift 8157375
  have htrace : WordTrace (prefixWord ++ tailWord_8157375) baseStart_8157375 baseEnd_8157375 := by
    simpa [prefixWord, tailWord_8157375, baseEnd_8157375] using wordTrace_append hprefix tailTrace_8157375
  have hstable : (prefixWord ++ tailWord_8157375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157375).length < 2 ^ (prefixWord ++ tailWord_8157375).sum := by decide
  have hdescent : baseEnd_8157375 < baseStart_8157375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157402 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2]
def baseStart_8157402 : Nat := 118140960795 + 8157402 * 2 ^ 59
def prefixEnd_8157402 : Nat := 4983230072969 + 3 ^ 40 * 8157402 * 2
def baseEnd_8157402 : Nat := 4188668117947798360859797

theorem tailTrace_8157402 : CollatzResearch.WordTrace tailWord_8157402 prefixEnd_8157402 4188668117947798360859797 := by
  unfold tailWord_8157402
  simp only [CollatzResearch.WordTrace]
  refine ⟨74381223398283300547628615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198349929062088801460342973 74381223398283300547628615)
  ·
    refine ⟨111571835097424950821442923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74381223398283300547628615 111571835097424950821442923)
    ·
      refine ⟨167357752646137426232164385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111571835097424950821442923 167357752646137426232164385)
      ·
        refine ⟨125518314484603069674123289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167357752646137426232164385 125518314484603069674123289)
        ·
          refine ⟨94138735863452302255592467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125518314484603069674123289 94138735863452302255592467)
          ·
            refine ⟨141208103795178453383388701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94138735863452302255592467 141208103795178453383388701)
            ·
              refine ⟨52953038923191920018770763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141208103795178453383388701 52953038923191920018770763)
              ·
                refine ⟨79429558384787880028156145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52953038923191920018770763 79429558384787880028156145)
                ·
                  refine ⟨59572168788590910021117109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79429558384787880028156145 59572168788590910021117109)
                  ·
                    refine ⟨5584890823930397814479729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59572168788590910021117109 5584890823930397814479729)
                    ·
                      refine ⟨4188668117947798360859797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584890823930397814479729 4188668117947798360859797)
                      ·
                        rfl

theorem cell23_8157402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_8157402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157402 prefixEnd_8157402 := by exact prefixLift 8157402
  have htrace : WordTrace (prefixWord ++ tailWord_8157402) baseStart_8157402 baseEnd_8157402 := by
    simpa [prefixWord, tailWord_8157402, baseEnd_8157402] using wordTrace_append hprefix tailTrace_8157402
  have hstable : (prefixWord ++ tailWord_8157402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157402).length < 2 ^ (prefixWord ++ tailWord_8157402).sum := by decide
  have hdescent : baseEnd_8157402 < baseStart_8157402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157410 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_8157410 : Nat := 118140960795 + 8157410 * 2 ^ 59
def prefixEnd_8157410 : Nat := 4983230072969 + 3 ^ 40 * 8157410 * 2
def baseEnd_8157410 : Nat := 4188672225793034329559761

theorem tailTrace_8157410 : CollatzResearch.WordTrace tailWord_8157410 prefixEnd_8157410 4188672225793034329559761 := by
  unfold tailWord_8157410
  simp only [CollatzResearch.WordTrace]
  refine ⟨74381296344276054889201421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198350123584736146371203789 74381296344276054889201421)
  ·
    refine ⟨27892986129103520583450533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74381296344276054889201421 27892986129103520583450533)
    ·
      refine ⟨5229934899206910109396975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27892986129103520583450533 5229934899206910109396975)
      ·
        refine ⟨7844902348810365164095463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229934899206910109396975 7844902348810365164095463)
        ·
          refine ⟨11767353523215547746143195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7844902348810365164095463 11767353523215547746143195)
          ·
            refine ⟨17651030284823321619214793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11767353523215547746143195 17651030284823321619214793)
            ·
              refine ⟨13238272713617491214411095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17651030284823321619214793 13238272713617491214411095)
              ·
                refine ⟨19857409070426236821616643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13238272713617491214411095 19857409070426236821616643)
                ·
                  refine ⟨29786113605639355232424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19857409070426236821616643 29786113605639355232424965)
                  ·
                    refine ⟨5584896301057379106079681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29786113605639355232424965 5584896301057379106079681)
                    ·
                      refine ⟨4188672225793034329559761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5584896301057379106079681 4188672225793034329559761)
                      ·
                        rfl

theorem cell23_8157410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_8157410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157410 prefixEnd_8157410 := by exact prefixLift 8157410
  have htrace : WordTrace (prefixWord ++ tailWord_8157410) baseStart_8157410 baseEnd_8157410 := by
    simpa [prefixWord, tailWord_8157410, baseEnd_8157410] using wordTrace_append hprefix tailTrace_8157410
  have hstable : (prefixWord ++ tailWord_8157410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157410).length < 2 ^ (prefixWord ++ tailWord_8157410).sum := by decide
  have hdescent : baseEnd_8157410 < baseStart_8157410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157452 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_8157452 : Nat := 118140960795 + 8157452 * 2 ^ 59
def prefixEnd_8157452 : Nat := 4983230072969 + 3 ^ 40 * 8157452 * 2
def baseEnd_8157452 : Nat := 4188693791980523165234567

theorem tailTrace_8157452 : CollatzResearch.WordTrace tailWord_8157452 prefixEnd_8157452 4188693791980523165234567 := by
  unfold tailWord_8157452
  simp only [CollatzResearch.WordTrace]
  refine ⟨148763358621476030364917305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198351144828634707153223073 148763358621476030364917305)
  ·
    refine ⟨111572518966107022773687979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148763358621476030364917305 111572518966107022773687979)
    ·
      refine ⟨167358778449160534160531969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111572518966107022773687979 167358778449160534160531969)
      ·
        refine ⟨125519083836870400620398977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167358778449160534160531969 125519083836870400620398977)
        ·
          refine ⟨94139312877652800465299233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125519083836870400620398977 94139312877652800465299233)
          ·
            refine ⟨70604484658239600348974425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94139312877652800465299233 70604484658239600348974425)
            ·
              refine ⟨52953363493679700261730819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70604484658239600348974425 52953363493679700261730819)
              ·
                refine ⟨79430045240519550392596229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52953363493679700261730819 79430045240519550392596229)
                ·
                  refine ⟨14893133482597415698611793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79430045240519550392596229 14893133482597415698611793)
                  ·
                    refine ⟨11169850111948061773958845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14893133482597415698611793 11169850111948061773958845)
                    ·
                      refine ⟨4188693791980523165234567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11169850111948061773958845 4188693791980523165234567)
                      ·
                        rfl

theorem cell23_8157452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_8157452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157452 prefixEnd_8157452 := by exact prefixLift 8157452
  have htrace : WordTrace (prefixWord ++ tailWord_8157452) baseStart_8157452 baseEnd_8157452 := by
    simpa [prefixWord, tailWord_8157452, baseEnd_8157452] using wordTrace_append hprefix tailTrace_8157452
  have hstable : (prefixWord ++ tailWord_8157452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157452).length < 2 ^ (prefixWord ++ tailWord_8157452).sum := by decide
  have hdescent : baseEnd_8157452 < baseStart_8157452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157475 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_8157475 : Nat := 118140960795 + 8157475 * 2 ^ 59
def prefixEnd_8157475 : Nat := 4983230072969 + 3 ^ 40 * 8157475 * 2
def baseEnd_8157475 : Nat := 4188705602035576575246961

theorem tailTrace_8157475 : CollatzResearch.WordTrace tailWord_8157475 prefixEnd_8157475 4188705602035576575246961 := by
  unfold tailWord_8157475
  simp only [CollatzResearch.WordTrace]
  refine ⟨297527556121868735657921879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198351704081245823771947919 297527556121868735657921879)
  ·
    refine ⟨446291334182803103486882819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297527556121868735657921879 446291334182803103486882819)
    ·
      refine ⟨669437001274204655230324229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446291334182803103486882819 669437001274204655230324229)
      ·
        refine ⟨125519437738913372855685793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 669437001274204655230324229 125519437738913372855685793)
        ·
          refine ⟨94139578304185029641764345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125519437738913372855685793 94139578304185029641764345)
          ·
            refine ⟨70604683728138772231323259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94139578304185029641764345 70604683728138772231323259)
            ·
              refine ⟨105907025592208158346984889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70604683728138772231323259 105907025592208158346984889)
              ·
                refine ⟨79430269194156118760238667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105907025592208158346984889 79430269194156118760238667)
                ·
                  refine ⟨119145403791234178140358001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79430269194156118760238667 119145403791234178140358001)
                  ·
                    refine ⟨89359052843425633605268501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119145403791234178140358001 89359052843425633605268501)
                    ·
                      refine ⟨4188705602035576575246961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89359052843425633605268501 4188705602035576575246961)
                      ·
                        rfl

theorem cell23_8157475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_8157475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157475 prefixEnd_8157475 := by exact prefixLift 8157475
  have htrace : WordTrace (prefixWord ++ tailWord_8157475) baseStart_8157475 baseEnd_8157475 := by
    simpa [prefixWord, tailWord_8157475, baseEnd_8157475] using wordTrace_append hprefix tailTrace_8157475
  have hstable : (prefixWord ++ tailWord_8157475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157475).length < 2 ^ (prefixWord ++ tailWord_8157475).sum := by decide
  have hdescent : baseEnd_8157475 < baseStart_8157475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157515 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 5, 6]
def baseStart_8157515 : Nat := 118140960795 + 8157515 * 2 ^ 59
def prefixEnd_8157515 : Nat := 4983230072969 + 3 ^ 40 * 8157515 * 2
def baseEnd_8157515 : Nat := 1396242047087252139582259

theorem tailTrace_8157515 : CollatzResearch.WordTrace tailWord_8157515 prefixEnd_8157515 1396242047087252139582259 := by
  unfold tailWord_8157515
  simp only [CollatzResearch.WordTrace]
  refine ⟨297529015041723822489377999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198352676694482548326251999 297529015041723822489377999)
  ·
    refine ⟨446293522562585733734066999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297529015041723822489377999 446293522562585733734066999)
    ·
      refine ⟨669440283843878600601100499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446293522562585733734066999 669440283843878600601100499)
      ·
        refine ⟨1004160425765817900901650749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669440283843878600601100499 1004160425765817900901650749)
        ·
          refine ⟨376560159662181712838119031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004160425765817900901650749 376560159662181712838119031)
          ·
            refine ⟨564840239493272569257178547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376560159662181712838119031 564840239493272569257178547)
            ·
              refine ⟨847260359239908853885767821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564840239493272569257178547 847260359239908853885767821)
              ·
                refine ⟨317722634714965820207162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847260359239908853885767821 317722634714965820207162933)
                ·
                  refine ⟨29786497004528045644421525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317722634714965820207162933 29786497004528045644421525)
                  ·
                    refine ⟨1396242047087252139582259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29786497004528045644421525 1396242047087252139582259)
                    ·
                      rfl

theorem cell23_8157515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_8157515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157515 prefixEnd_8157515 := by exact prefixLift 8157515
  have htrace : WordTrace (prefixWord ++ tailWord_8157515) baseStart_8157515 baseEnd_8157515 := by
    simpa [prefixWord, tailWord_8157515, baseEnd_8157515] using wordTrace_append hprefix tailTrace_8157515
  have hstable : (prefixWord ++ tailWord_8157515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157515).length < 2 ^ (prefixWord ++ tailWord_8157515).sum := by decide
  have hdescent : baseEnd_8157515 < baseStart_8157515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157536 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 1, 5]
def baseStart_8157536 : Nat := 118140960795 + 8157536 * 2 ^ 59
def prefixEnd_8157536 : Nat := 4983230072969 + 3 ^ 40 * 8157536 * 2
def baseEnd_8157536 : Nat := 1396245641451833612194727

theorem tailTrace_8157536 : CollatzResearch.WordTrace tailWord_8157536 prefixEnd_8157536 1396245641451833612194727 := by
  unfold tailWord_8157536
  simp only [CollatzResearch.WordTrace]
  refine ⟨148764890487323871537946231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198353187316431828717261641 148764890487323871537946231)
  ·
    refine ⟨223147335730985807306919347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148764890487323871537946231 223147335730985807306919347)
    ·
      refine ⟨334721003596478710960379021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223147335730985807306919347 334721003596478710960379021)
      ·
        refine ⟨125520376348679516610142133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334721003596478710960379021 125520376348679516610142133)
        ·
          refine ⟨11767535282688704682200825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125520376348679516610142133 11767535282688704682200825)
          ·
            refine ⟨8825651462016528511650619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11767535282688704682200825 8825651462016528511650619)
            ·
              refine ⟨13238477193024792767475929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8825651462016528511650619 13238477193024792767475929)
              ·
                refine ⟨9928857894768594575606947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13238477193024792767475929 9928857894768594575606947)
                ·
                  refine ⟨14893286842152891863410421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928857894768594575606947 14893286842152891863410421)
                  ·
                    refine ⟨1396245641451833612194727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14893286842152891863410421 1396245641451833612194727)
                    ·
                      rfl

theorem cell23_8157536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_8157536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157536 prefixEnd_8157536 := by exact prefixLift 8157536
  have htrace : WordTrace (prefixWord ++ tailWord_8157536) baseStart_8157536 baseEnd_8157536 := by
    simpa [prefixWord, tailWord_8157536, baseEnd_8157536] using wordTrace_append hprefix tailTrace_8157536
  have hstable : (prefixWord ++ tailWord_8157536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157536).length < 2 ^ (prefixWord ++ tailWord_8157536).sum := by decide
  have hdescent : baseEnd_8157536 < baseStart_8157536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157545 : List Nat := [1, 2, 1, 1, 1, 3, 3, 11]
def baseStart_8157545 : Nat := 118140960795 + 8157545 * 2 ^ 59
def prefixEnd_8157545 : Nat := 4983230072969 + 3 ^ 40 * 8157545 * 2
def baseEnd_8157545 : Nat := 155138575765977455606357

theorem tailTrace_8157545 : CollatzResearch.WordTrace tailWord_8157545 prefixEnd_8157545 155138575765977455606357 := by
  unfold tailWord_8157545
  simp only [CollatzResearch.WordTrace]
  refine ⟨297530109231615137612970089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198353406154410091741980059 297530109231615137612970089)
  ·
    refine ⟨223147581923711353209727567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297530109231615137612970089 223147581923711353209727567)
    ·
      refine ⟨334721372885567029814591351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223147581923711353209727567 334721372885567029814591351)
      ·
        refine ⟨502082059328350544721887027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334721372885567029814591351 502082059328350544721887027)
        ·
          refine ⟨753123088992525817082830541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502082059328350544721887027 753123088992525817082830541)
          ·
            refine ⟨282421158372197181406061453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 753123088992525817082830541 282421158372197181406061453)
            ·
              refine ⟨105907934389573943027273045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282421158372197181406061453 105907934389573943027273045)
              ·
                refine ⟨155138575765977455606357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105907934389573943027273045 155138575765977455606357)
                ·
                  rfl

theorem cell23_8157545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 11].length) (baseStart_8157545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157545 prefixEnd_8157545 := by exact prefixLift 8157545
  have htrace : WordTrace (prefixWord ++ tailWord_8157545) baseStart_8157545 baseEnd_8157545 := by
    simpa [prefixWord, tailWord_8157545, baseEnd_8157545] using wordTrace_append hprefix tailTrace_8157545
  have hstable : (prefixWord ++ tailWord_8157545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157545).length < 2 ^ (prefixWord ++ tailWord_8157545).sum := by decide
  have hdescent : baseEnd_8157545 < baseStart_8157545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157552 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_8157552 : Nat := 118140960795 + 8157552 * 2 ^ 59
def prefixEnd_8157552 : Nat := 4983230072969 + 3 ^ 40 * 8157552 * 2
def baseEnd_8157552 : Nat := 4188745140045972773984107

theorem tailTrace_8157552 : CollatzResearch.WordTrace tailWord_8157552 prefixEnd_8157552 4188745140045972773984107 := by
  unfold tailWord_8157552
  simp only [CollatzResearch.WordTrace]
  refine ⟨148765182271294888904237455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198353576361726518538983273 148765182271294888904237455)
  ·
    refine ⟨223147773406942333356356183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148765182271294888904237455 223147773406942333356356183)
    ·
      refine ⟨334721660110413500034534275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223147773406942333356356183 334721660110413500034534275)
      ·
        refine ⟨502082490165620250051801413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334721660110413500034534275 502082490165620250051801413)
        ·
          refine ⟨94140466906053796884712765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 502082490165620250051801413 94140466906053796884712765)
          ·
            refine ⟨35302675089770173831767287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94140466906053796884712765 35302675089770173831767287)
            ·
              refine ⟨52954012634655260747650931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35302675089770173831767287 52954012634655260747650931)
              ·
                refine ⟨79431018951982891121476397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52954012634655260747650931 79431018951982891121476397)
                ·
                  refine ⟨29786632106993584170553649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79431018951982891121476397 29786632106993584170553649)
                  ·
                    refine ⟨22339974080245188127915237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29786632106993584170553649 22339974080245188127915237)
                    ·
                      refine ⟨4188745140045972773984107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22339974080245188127915237 4188745140045972773984107)
                      ·
                        rfl

theorem cell23_8157552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_8157552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157552 prefixEnd_8157552 := by exact prefixLift 8157552
  have htrace : WordTrace (prefixWord ++ tailWord_8157552) baseStart_8157552 baseEnd_8157552 := by
    simpa [prefixWord, tailWord_8157552, baseEnd_8157552] using wordTrace_append hprefix tailTrace_8157552
  have hstable : (prefixWord ++ tailWord_8157552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157552).length < 2 ^ (prefixWord ++ tailWord_8157552).sum := by decide
  have hdescent : baseEnd_8157552 < baseStart_8157552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157589 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_8157589 : Nat := 118140960795 + 8157589 * 2 ^ 59
def prefixEnd_8157589 : Nat := 4983230072969 + 3 ^ 40 * 8157589 * 2
def baseEnd_8157589 : Nat := 4188764138830189129221437

theorem tailTrace_8157589 : CollatzResearch.WordTrace tailWord_8157589 prefixEnd_8157589 4188764138830189129221437 := by
  unfold tailWord_8157589
  simp only [CollatzResearch.WordTrace]
  refine ⟨297531714043455733127571821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198354476028970488751714547 297531714043455733127571821)
  ·
    refine ⟨111574392766295899922839433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297531714043455733127571821 111574392766295899922839433)
    ·
      refine ⟨83680794574721924942129575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111574392766295899922839433 83680794574721924942129575)
      ·
        refine ⟨125521191862082887413194363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83680794574721924942129575 125521191862082887413194363)
        ·
          refine ⟨188281787793124331119791545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125521191862082887413194363 188281787793124331119791545)
          ·
            refine ⟨141211340844843248339843659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188281787793124331119791545 141211340844843248339843659)
            ·
              refine ⟨211817011267264872509765489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141211340844843248339843659 211817011267264872509765489)
              ·
                refine ⟨158862758450448654382324117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211817011267264872509765489 158862758450448654382324117)
                ·
                  refine ⟨7446691802364780674171443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158862758450448654382324117 7446691802364780674171443)
                  ·
                    refine ⟨11170037703547171011257165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7446691802364780674171443 11170037703547171011257165)
                    ·
                      refine ⟨4188764138830189129221437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11170037703547171011257165 4188764138830189129221437)
                      ·
                        rfl

theorem cell23_8157589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_8157589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157589 prefixEnd_8157589 := by exact prefixLift 8157589
  have htrace : WordTrace (prefixWord ++ tailWord_8157589) baseStart_8157589 baseEnd_8157589 := by
    simpa [prefixWord, tailWord_8157589, baseEnd_8157589] using wordTrace_append hprefix tailTrace_8157589
  have hstable : (prefixWord ++ tailWord_8157589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157589).length < 2 ^ (prefixWord ++ tailWord_8157589).sum := by decide
  have hdescent : baseEnd_8157589 < baseStart_8157589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157623 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_8157623 : Nat := 118140960795 + 8157623 * 2 ^ 59
def prefixEnd_8157623 : Nat := 4983230072969 + 3 ^ 40 * 8157623 * 2
def baseEnd_8157623 : Nat := 4188781597172441996196281

theorem tailTrace_8157623 : CollatzResearch.WordTrace tailWord_8157623 prefixEnd_8157623 4188781597172441996196281 := by
  unfold tailWord_8157623
  simp only [CollatzResearch.WordTrace]
  refine ⟨297532954125332556934309523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198355302750221704622873015 297532954125332556934309523)
  ·
    refine ⟨446299431187998835401464285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297532954125332556934309523 446299431187998835401464285)
    ·
      refine ⟨167362286695499563275549107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446299431187998835401464285 167362286695499563275549107)
      ·
        refine ⟨251043430043249344913323661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167362286695499563275549107 251043430043249344913323661)
        ·
          refine ⟨94141286266218504342496373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251043430043249344913323661 94141286266218504342496373)
          ·
            refine ⟨8825745587457984782109035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94141286266218504342496373 8825745587457984782109035)
            ·
              refine ⟨13238618381186977173163553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8825745587457984782109035 13238618381186977173163553)
              ·
                refine ⟨9928963785890232879872665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13238618381186977173163553 9928963785890232879872665)
                ·
                  refine ⟨7446722839417674659904499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9928963785890232879872665 7446722839417674659904499)
                  ·
                    refine ⟨11170084259126511989856749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7446722839417674659904499 11170084259126511989856749)
                    ·
                      refine ⟨4188781597172441996196281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11170084259126511989856749 4188781597172441996196281)
                      ·
                        rfl

theorem cell23_8157623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_8157623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157623 prefixEnd_8157623 := by exact prefixLift 8157623
  have htrace : WordTrace (prefixWord ++ tailWord_8157623) baseStart_8157623 baseEnd_8157623 := by
    simpa [prefixWord, tailWord_8157623, baseEnd_8157623] using wordTrace_append hprefix tailTrace_8157623
  have hstable : (prefixWord ++ tailWord_8157623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157623).length < 2 ^ (prefixWord ++ tailWord_8157623).sum := by decide
  have hdescent : baseEnd_8157623 < baseStart_8157623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157632 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_8157632 : Nat := 118140960795 + 8157632 * 2 ^ 59
def prefixEnd_8157632 : Nat := 4983230072969 + 3 ^ 40 * 8157632 * 2
def baseEnd_8157632 : Nat := 4188786218498332460983739

theorem tailTrace_8157632 : CollatzResearch.WordTrace tailWord_8157632 prefixEnd_8157632 4188786218498332460983739 := by
  unfold tailWord_8157632
  simp only [CollatzResearch.WordTrace]
  refine ⟨148766641191149975735693575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198355521588199967647591433 148766641191149975735693575)
  ·
    refine ⟨223149961786724963603540363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148766641191149975735693575 223149961786724963603540363)
    ·
      refine ⟨334724942680087445405310545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223149961786724963603540363 334724942680087445405310545)
      ·
        refine ⟨251043707010065584053982909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334724942680087445405310545 251043707010065584053982909)
        ·
          refine ⟨94141390128774594020243591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251043707010065584053982909 94141390128774594020243591)
          ·
            refine ⟨141212085193161891030365387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94141390128774594020243591 141212085193161891030365387)
            ·
              refine ⟨211818127789742836545548081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141212085193161891030365387 211818127789742836545548081)
              ·
                refine ⟨158863595842307127409161061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211818127789742836545548081 158863595842307127409161061)
                ·
                  refine ⟨29786924220432586389217699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158863595842307127409161061 29786924220432586389217699)
                  ·
                    refine ⟨44680386330648879583826549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29786924220432586389217699 44680386330648879583826549)
                    ·
                      refine ⟨4188786218498332460983739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44680386330648879583826549 4188786218498332460983739)
                      ·
                        rfl

theorem cell23_8157632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_8157632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157632 prefixEnd_8157632 := by exact prefixLift 8157632
  have htrace : WordTrace (prefixWord ++ tailWord_8157632) baseStart_8157632 baseEnd_8157632 := by
    simpa [prefixWord, tailWord_8157632, baseEnd_8157632] using wordTrace_append hprefix tailTrace_8157632
  have hstable : (prefixWord ++ tailWord_8157632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157632).length < 2 ^ (prefixWord ++ tailWord_8157632).sum := by decide
  have hdescent : baseEnd_8157632 < baseStart_8157632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157697 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_8157697 : Nat := 118140960795 + 8157697 * 2 ^ 59
def prefixEnd_8157697 : Nat := 4983230072969 + 3 ^ 40 * 8157697 * 2
def baseEnd_8157697 : Nat := 4188819594740874706670941

theorem tailTrace_8157697 : CollatzResearch.WordTrace tailWord_8157697 prefixEnd_8157697 4188819594740874706670941 := by
  unfold tailWord_8157697
  simp only [CollatzResearch.WordTrace]
  refine ⟨297535653127064467572503345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198357102084709645048335563 297535653127064467572503345)
  ·
    refine ⟨223151739845298350679377509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297535653127064467572503345 223151739845298350679377509)
    ·
      refine ⟨41840951220993440752383283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223151739845298350679377509 41840951220993440752383283)
      ·
        refine ⟨62761426831490161128574925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41840951220993440752383283 62761426831490161128574925)
        ·
          refine ⟨23535535061808810423215597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62761426831490161128574925 23535535061808810423215597)
          ·
            refine ⟨8825825648178303908705849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23535535061808810423215597 8825825648178303908705849)
            ·
              refine ⟨6619369236133727931529387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8825825648178303908705849 6619369236133727931529387)
              ·
                refine ⟨9929053854200591897294081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619369236133727931529387 9929053854200591897294081)
                ·
                  refine ⟨7446790390650443922970561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9929053854200591897294081 7446790390650443922970561)
                  ·
                    refine ⟨5585092792987832942227921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7446790390650443922970561 5585092792987832942227921)
                    ·
                      refine ⟨4188819594740874706670941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585092792987832942227921 4188819594740874706670941)
                      ·
                        rfl

theorem cell23_8157697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_8157697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157697 prefixEnd_8157697 := by exact prefixLift 8157697
  have htrace : WordTrace (prefixWord ++ tailWord_8157697) baseStart_8157697 baseEnd_8157697 := by
    simpa [prefixWord, tailWord_8157697, baseEnd_8157697] using wordTrace_append hprefix tailTrace_8157697
  have hstable : (prefixWord ++ tailWord_8157697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157697).length < 2 ^ (prefixWord ++ tailWord_8157697).sum := by decide
  have hdescent : baseEnd_8157697 < baseStart_8157697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157759 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 6]
def baseStart_8157759 : Nat := 118140960795 + 8157759 * 2 ^ 59
def prefixEnd_8157759 : Nat := 4983230072969 + 3 ^ 40 * 8157759 * 2
def baseEnd_8157759 : Nat := 465427936726828162677295

theorem tailTrace_8157759 : CollatzResearch.WordTrace tailWord_8157759 prefixEnd_8157759 465427936726828162677295 := by
  unfold tailWord_8157759
  simp only [CollatzResearch.WordTrace]
  refine ⟨297537914452839852161260331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198358609635226568107506887 297537914452839852161260331)
  ·
    refine ⟨446306871679259778241890497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297537914452839852161260331 446306871679259778241890497)
    ·
      refine ⟨334730153759444833681417873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446306871679259778241890497 334730153759444833681417873)
      ·
        refine ⟨251047615319583625261063405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334730153759444833681417873 251047615319583625261063405)
        ·
          refine ⟨94142855744843859472898777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251047615319583625261063405 94142855744843859472898777)
          ·
            refine ⟨70607141808632894604674083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94142855744843859472898777 70607141808632894604674083)
            ·
              refine ⟨105910712712949341907011125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70607141808632894604674083 105910712712949341907011125)
              ·
                refine ⟨9929129316839000803782293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105910712712949341907011125 9929129316839000803782293)
                ·
                  refine ⟨465427936726828162677295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9929129316839000803782293 465427936726828162677295)
                  ·
                    rfl

theorem cell23_8157759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 6].length) (baseStart_8157759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157759 prefixEnd_8157759 := by exact prefixLift 8157759
  have htrace : WordTrace (prefixWord ++ tailWord_8157759) baseStart_8157759 baseEnd_8157759 := by
    simpa [prefixWord, tailWord_8157759, baseEnd_8157759] using wordTrace_append hprefix tailTrace_8157759
  have hstable : (prefixWord ++ tailWord_8157759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157759).length < 2 ^ (prefixWord ++ tailWord_8157759).sum := by decide
  have hdescent : baseEnd_8157759 < baseStart_8157759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157773 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_8157773 : Nat := 118140960795 + 8157773 * 2 ^ 59
def prefixEnd_8157773 : Nat := 4983230072969 + 3 ^ 40 * 8157773 * 2
def baseEnd_8157773 : Nat := 4188858619270616409320591

theorem tailTrace_8157773 : CollatzResearch.WordTrace tailWord_8157773 prefixEnd_8157773 4188858619270616409320591 := by
  unfold tailWord_8157773
  simp only [CollatzResearch.WordTrace]
  refine ⟨297538425074789132552269973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198358950049859421701513315 297538425074789132552269973)
  ·
    refine ⟨13947113675380740588387655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297538425074789132552269973 13947113675380740588387655)
    ·
      refine ⟨20920670513071110882581483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947113675380740588387655 20920670513071110882581483)
      ·
        refine ⟨31381005769606666323872225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20920670513071110882581483 31381005769606666323872225)
        ·
          refine ⟨23535754327204999742904169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31381005769606666323872225 23535754327204999742904169)
          ·
            refine ⟨17651815745403749807178127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23535754327204999742904169 17651815745403749807178127)
            ·
              refine ⟨26477723618105624710767191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17651815745403749807178127 26477723618105624710767191)
              ·
                refine ⟨39716585427158437066150787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26477723618105624710767191 39716585427158437066150787)
                ·
                  refine ⟨59574878140737655599226181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39716585427158437066150787 59574878140737655599226181)
                  ·
                    refine ⟨11170289651388310424854909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59574878140737655599226181 11170289651388310424854909)
                    ·
                      refine ⟨4188858619270616409320591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11170289651388310424854909 4188858619270616409320591)
                      ·
                        rfl

theorem cell23_8157773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_8157773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157773 prefixEnd_8157773 := by exact prefixLift 8157773
  have htrace : WordTrace (prefixWord ++ tailWord_8157773) baseStart_8157773 baseEnd_8157773 := by
    simpa [prefixWord, tailWord_8157773, baseEnd_8157773] using wordTrace_append hprefix tailTrace_8157773
  have hstable : (prefixWord ++ tailWord_8157773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157773).length < 2 ^ (prefixWord ++ tailWord_8157773).sum := by decide
  have hdescent : baseEnd_8157773 < baseStart_8157773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157780 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_8157780 : Nat := 118140960795 + 8157780 * 2 ^ 59
def prefixEnd_8157780 : Nat := 4983230072969 + 3 ^ 40 * 8157780 * 2
def baseEnd_8157780 : Nat := 1396287404545065960644353

theorem tailTrace_8157780 : CollatzResearch.WordTrace tailWord_8157780 prefixEnd_8157780 1396287404545065960644353 := by
  unfold tailWord_8157780
  simp only [CollatzResearch.WordTrace]
  refine ⟨148769340192881886373887397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198359120257175848498516529 148769340192881886373887397)
  ·
    refine ⟨27894251286165353695103887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148769340192881886373887397 27894251286165353695103887)
    ·
      refine ⟨41841376929248030542655831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27894251286165353695103887 41841376929248030542655831)
      ·
        refine ⟨62762065393872045813983747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41841376929248030542655831 62762065393872045813983747)
        ·
          refine ⟨94143098090808068720975621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62762065393872045813983747 94143098090808068720975621)
          ·
            refine ⟨17651830892026512885182929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94143098090808068720975621 17651830892026512885182929)
            ·
              refine ⟨13238873169019884663887197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17651830892026512885182929 13238873169019884663887197)
              ·
                refine ⟨4964577438382456748957699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13238873169019884663887197 4964577438382456748957699)
                ·
                  refine ⟨7446866157573685123436549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964577438382456748957699 7446866157573685123436549)
                  ·
                    refine ⟨1396287404545065960644353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7446866157573685123436549 1396287404545065960644353)
                    ·
                      rfl

theorem cell23_8157780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_8157780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157780 prefixEnd_8157780 := by exact prefixLift 8157780
  have htrace : WordTrace (prefixWord ++ tailWord_8157780) baseStart_8157780 baseEnd_8157780 := by
    simpa [prefixWord, tailWord_8157780, baseEnd_8157780] using wordTrace_append hprefix tailTrace_8157780
  have hstable : (prefixWord ++ tailWord_8157780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157780).length < 2 ^ (prefixWord ++ tailWord_8157780).sum := by decide
  have hdescent : baseEnd_8157780 < baseStart_8157780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157819 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 1, 6]
def baseStart_8157819 : Nat := 118140960795 + 8157819 * 2 ^ 59
def prefixEnd_8157819 : Nat := 4983230072969 + 3 ^ 40 * 8157819 * 2
def baseEnd_8157819 : Nat := 1396294079793574409781793

theorem tailTrace_8157819 : CollatzResearch.WordTrace tailWord_8157819 prefixEnd_8157819 1396294079793574409781793 := by
  unfold tailWord_8157819
  simp only [CollatzResearch.WordTrace]
  refine ⟨297540102832622482408444511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198360068555081654938963007 297540102832622482408444511)
  ·
    refine ⟨446310154248933723612666767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297540102832622482408444511 446310154248933723612666767)
    ·
      refine ⟨669465231373400585419000151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446310154248933723612666767 669465231373400585419000151)
      ·
        refine ⟨1004197847060100878128500227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669465231373400585419000151 1004197847060100878128500227)
        ·
          refine ⟨1506296770590151317192750341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004197847060100878128500227 1506296770590151317192750341)
          ·
            refine ⟨282430644485653371973640689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1506296770590151317192750341 282430644485653371973640689)
            ·
              refine ⟨211822983364240028980230517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282430644485653371973640689 211822983364240028980230517)
              ·
                refine ⟨19858404690397502716896611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211822983364240028980230517 19858404690397502716896611)
                ·
                  refine ⟨29787607035596254075344917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19858404690397502716896611 29787607035596254075344917)
                  ·
                    refine ⟨1396294079793574409781793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29787607035596254075344917 1396294079793574409781793)
                    ·
                      rfl

theorem cell23_8157819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 6].length) (baseStart_8157819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157819 prefixEnd_8157819 := by exact prefixLift 8157819
  have htrace : WordTrace (prefixWord ++ tailWord_8157819) baseStart_8157819 baseEnd_8157819 := by
    simpa [prefixWord, tailWord_8157819, baseEnd_8157819] using wordTrace_append hprefix tailTrace_8157819
  have hstable : (prefixWord ++ tailWord_8157819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157819).length < 2 ^ (prefixWord ++ tailWord_8157819).sum := by decide
  have hdescent : baseEnd_8157819 < baseStart_8157819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157854 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_8157854 : Nat := 118140960795 + 8157854 * 2 ^ 59
def prefixEnd_8157854 : Nat := 4983230072969 + 3 ^ 40 * 8157854 * 2
def baseEnd_8157854 : Nat := 4188900211203630592407719

theorem tailTrace_8157854 : CollatzResearch.WordTrace tailWord_8157854 prefixEnd_8157854 4188900211203630592407719 := by
  unfold tailWord_8157854
  simp only [CollatzResearch.WordTrace]
  refine ⟨37192672423436960423246077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198360919591663788923979077 37192672423436960423246077)
  ·
    refine ⟨13947252158788860158717279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37192672423436960423246077 13947252158788860158717279)
    ·
      refine ⟨20920878238183290238075919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947252158788860158717279 20920878238183290238075919)
      ·
        refine ⟨31381317357274935357113879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20920878238183290238075919 31381317357274935357113879)
        ·
          refine ⟨47071976035912403035670819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31381317357274935357113879 47071976035912403035670819)
          ·
            refine ⟨70607964053868604553506229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47071976035912403035670819 70607964053868604553506229)
            ·
              refine ⟨6619496630050181676891209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70607964053868604553506229 6619496630050181676891209)
              ·
                refine ⟨4964622472537636257668407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619496630050181676891209 4964622472537636257668407)
                ·
                  refine ⟨7446933708806454386502611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964622472537636257668407 7446933708806454386502611)
                  ·
                    refine ⟨11170400563209681579753917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7446933708806454386502611 11170400563209681579753917)
                    ·
                      refine ⟨4188900211203630592407719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11170400563209681579753917 4188900211203630592407719)
                      ·
                        rfl

theorem cell23_8157854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_8157854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157854 prefixEnd_8157854 := by exact prefixLift 8157854
  have htrace : WordTrace (prefixWord ++ tailWord_8157854) baseStart_8157854 baseEnd_8157854 := by
    simpa [prefixWord, tailWord_8157854, baseEnd_8157854] using wordTrace_append hprefix tailTrace_8157854
  have hstable : (prefixWord ++ tailWord_8157854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157854).length < 2 ^ (prefixWord ++ tailWord_8157854).sum := by decide
  have hdescent : baseEnd_8157854 < baseStart_8157854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157936 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_8157936 : Nat := 118140960795 + 8157936 * 2 ^ 59
def prefixEnd_8157936 : Nat := 4983230072969 + 3 ^ 40 * 8157936 * 2
def baseEnd_8157936 : Nat := 4188942316617299271582341

theorem tailTrace_8157936 : CollatzResearch.WordTrace tailWord_8157936 prefixEnd_8157936 4188942316617299271582341 := by
  unfold tailWord_8157936
  simp only [CollatzResearch.WordTrace]
  refine ⟨148772185086599305695226831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198362913448799074260302441 148772185086599305695226831)
  ·
    refine ⟨223158277629898958542840247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148772185086599305695226831 223158277629898958542840247)
    ·
      refine ⟨334737416444848437814260371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223158277629898958542840247 334737416444848437814260371)
      ·
        refine ⟨502106124667272656721390557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334737416444848437814260371 502106124667272656721390557)
        ·
          refine ⟨188289796750227246270521459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502106124667272656721390557 188289796750227246270521459)
          ·
            refine ⟨282434695125340869405782189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188289796750227246270521459 282434695125340869405782189)
            ·
              refine ⟨105913010672002826027168321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282434695125340869405782189 105913010672002826027168321)
              ·
                refine ⟨79434758004002119520376241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105913010672002826027168321 79434758004002119520376241)
                ·
                  refine ⟨59576068503001589640282181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79434758004002119520376241 59576068503001589640282181)
                  ·
                    refine ⟨11170512844312798057552909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59576068503001589640282181 11170512844312798057552909)
                    ·
                      refine ⟨4188942316617299271582341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11170512844312798057552909 4188942316617299271582341)
                      ·
                        rfl

theorem cell23_8157936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_8157936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157936 prefixEnd_8157936 := by exact prefixLift 8157936
  have htrace : WordTrace (prefixWord ++ tailWord_8157936) baseStart_8157936 baseEnd_8157936 := by
    simpa [prefixWord, tailWord_8157936, baseEnd_8157936] using wordTrace_append hprefix tailTrace_8157936
  have hstable : (prefixWord ++ tailWord_8157936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157936).length < 2 ^ (prefixWord ++ tailWord_8157936).sum := by decide
  have hdescent : baseEnd_8157936 < baseStart_8157936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157954 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_8157954 : Nat := 118140960795 + 8157954 * 2 ^ 59
def prefixEnd_8157954 : Nat := 4983230072969 + 3 ^ 40 * 8157954 * 2
def baseEnd_8157954 : Nat := 4188951559269080201157259

theorem tailTrace_8157954 : CollatzResearch.WordTrace tailWord_8157954 prefixEnd_8157954 4188951559269080201157259 := by
  unfold tailWord_8157954
  simp only [CollatzResearch.WordTrace]
  refine ⟨74386256671783350116152229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198363351124755600309739277 74386256671783350116152229)
  ·
    refine ⟨13947423125959378146778543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74386256671783350116152229 13947423125959378146778543)
    ·
      refine ⟨20921134688939067220167815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947423125959378146778543 20921134688939067220167815)
      ·
        refine ⟨31381702033408600830251723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20921134688939067220167815 31381702033408600830251723)
        ·
          refine ⟨47072553050112901245377585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31381702033408600830251723 47072553050112901245377585)
          ·
            refine ⟨35304414787584675934033189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47072553050112901245377585 35304414787584675934033189)
            ·
              refine ⟨6619577772672126737631223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35304414787584675934033189 6619577772672126737631223)
              ·
                refine ⟨9929366659008190106446835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619577772672126737631223 9929366659008190106446835)
                ·
                  refine ⟨14894049988512285159670253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9929366659008190106446835 14894049988512285159670253)
                  ·
                    refine ⟨5585268745692106934876345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14894049988512285159670253 5585268745692106934876345)
                    ·
                      refine ⟨4188951559269080201157259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585268745692106934876345 4188951559269080201157259)
                      ·
                        rfl

theorem cell23_8157954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_8157954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157954 prefixEnd_8157954 := by exact prefixLift 8157954
  have htrace : WordTrace (prefixWord ++ tailWord_8157954) baseStart_8157954 baseEnd_8157954 := by
    simpa [prefixWord, tailWord_8157954, baseEnd_8157954] using wordTrace_append hprefix tailTrace_8157954
  have hstable : (prefixWord ++ tailWord_8157954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157954).length < 2 ^ (prefixWord ++ tailWord_8157954).sum := by decide
  have hdescent : baseEnd_8157954 < baseStart_8157954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157956 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 9]
def baseStart_8157956 : Nat := 118140960795 + 8157956 * 2 ^ 59
def prefixEnd_8157956 : Nat := 4983230072969 + 3 ^ 40 * 8157956 * 2
def baseEnd_8157956 : Nat := 465439176247821021481361

theorem tailTrace_8157956 : CollatzResearch.WordTrace tailWord_8157956 prefixEnd_8157956 465439176247821021481361 := by
  unfold tailWord_8157956
  simp only [CollatzResearch.WordTrace]
  refine ⟨148772549816563077403090861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198363399755417436537454481 148772549816563077403090861)
  ·
    refine ⟨55789706181211154026159073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148772549816563077403090861 55789706181211154026159073)
    ·
      refine ⟨41842279635908365519619305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55789706181211154026159073 41842279635908365519619305)
      ·
        refine ⟨31381709726931274139714479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41842279635908365519619305 31381709726931274139714479)
        ·
          refine ⟨47072564590396911209571719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31381709726931274139714479 47072564590396911209571719)
          ·
            refine ⟨70608846885595366814357579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47072564590396911209571719 70608846885595366814357579)
            ·
              refine ⟨105913270328393050221536369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70608846885595366814357579 105913270328393050221536369)
              ·
                refine ⟨79434952746294787666152277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105913270328393050221536369 79434952746294787666152277)
                ·
                  refine ⟨465439176247821021481361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79434952746294787666152277 465439176247821021481361)
                  ·
                    rfl

theorem cell23_8157956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_8157956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157956 prefixEnd_8157956 := by exact prefixLift 8157956
  have htrace : WordTrace (prefixWord ++ tailWord_8157956) baseStart_8157956 baseEnd_8157956 := by
    simpa [prefixWord, tailWord_8157956, baseEnd_8157956] using wordTrace_append hprefix tailTrace_8157956
  have hstable : (prefixWord ++ tailWord_8157956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157956).length < 2 ^ (prefixWord ++ tailWord_8157956).sum := by decide
  have hdescent : baseEnd_8157956 < baseStart_8157956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157973 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 5]
def baseStart_8157973 : Nat := 118140960795 + 8157973 * 2 ^ 59
def prefixEnd_8157973 : Nat := 4983230072969 + 3 ^ 40 * 8157973 * 2
def baseEnd_8157973 : Nat := 465440146155723958535519

theorem tailTrace_8157973 : CollatzResearch.WordTrace tailWord_8157973 prefixEnd_8157973 465440146155723958535519 := by
  unfold tailWord_8157973
  simp only [CollatzResearch.WordTrace]
  refine ⟨297545719674064566709550573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198363813116043044473033715 297545719674064566709550573)
  ·
    refine ⟨111579644877774212516081465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297545719674064566709550573 111579644877774212516081465)
    ·
      refine ⟨83684733658330659387061099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111579644877774212516081465 83684733658330659387061099)
      ·
        refine ⟨125527100487495989080591649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83684733658330659387061099 125527100487495989080591649)
        ·
          refine ⟨94145325365621991810443737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125527100487495989080591649 94145325365621991810443737)
          ·
            refine ⟨70608994024216493857832803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94145325365621991810443737 70608994024216493857832803)
            ·
              refine ⟨105913491036324740786749205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70608994024216493857832803 105913491036324740786749205)
              ·
                refine ⟨4964694892327722224378869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105913491036324740786749205 4964694892327722224378869)
                ·
                  refine ⟨465440146155723958535519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4964694892327722224378869 465440146155723958535519)
                  ·
                    rfl

theorem cell23_8157973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_8157973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157973 prefixEnd_8157973 := by exact prefixLift 8157973
  have htrace : WordTrace (prefixWord ++ tailWord_8157973) baseStart_8157973 baseEnd_8157973 := by
    simpa [prefixWord, tailWord_8157973, baseEnd_8157973] using wordTrace_append hprefix tailTrace_8157973
  have hstable : (prefixWord ++ tailWord_8157973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157973).length < 2 ^ (prefixWord ++ tailWord_8157973).sum := by decide
  have hdescent : baseEnd_8157973 < baseStart_8157973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157983 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_8157983 : Nat := 118140960795 + 8157983 * 2 ^ 59
def prefixEnd_8157983 : Nat := 4983230072969 + 3 ^ 40 * 8157983 * 2
def baseEnd_8157983 : Nat := 4188966450208060587694625

theorem tailTrace_8157983 : CollatzResearch.WordTrace tailWord_8157983 prefixEnd_8157983 4188966450208060587694625 := by
  unfold tailWord_8157983
  simp only [CollatzResearch.WordTrace]
  refine ⟨297546084404028338417414603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198364056269352225611609735 297546084404028338417414603)
  ·
    refine ⟨446319126606042507626121905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297546084404028338417414603 446319126606042507626121905)
    ·
      refine ⟨334739344954531880719591429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446319126606042507626121905 334739344954531880719591429)
      ·
        refine ⟨62763627178974727634923393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334739344954531880719591429 62763627178974727634923393)
        ·
          refine ⟨47072720384231045726192545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62763627178974727634923393 47072720384231045726192545)
          ·
            refine ⟨35304540288173284294644409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47072720384231045726192545 35304540288173284294644409)
            ·
              refine ⟨26478405216129963220983307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35304540288173284294644409 26478405216129963220983307)
              ·
                refine ⟨39717607824194944831474961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26478405216129963220983307 39717607824194944831474961)
                ·
                  refine ⟨29788205868146208623606221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39717607824194944831474961 29788205868146208623606221)
                  ·
                    refine ⟨11170577200554828233852333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29788205868146208623606221 11170577200554828233852333)
                    ·
                      refine ⟨4188966450208060587694625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11170577200554828233852333 4188966450208060587694625)
                      ·
                        rfl

theorem cell23_8157983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_8157983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157983 prefixEnd_8157983 := by exact prefixLift 8157983
  have htrace : WordTrace (prefixWord ++ tailWord_8157983) baseStart_8157983 baseEnd_8157983 := by
    simpa [prefixWord, tailWord_8157983, baseEnd_8157983] using wordTrace_append hprefix tailTrace_8157983
  have hstable : (prefixWord ++ tailWord_8157983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157983).length < 2 ^ (prefixWord ++ tailWord_8157983).sum := by decide
  have hdescent : baseEnd_8157983 < baseStart_8157983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8157984 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 2, 2, 2]
def baseStart_8157984 : Nat := 118140960795 + 8157984 * 2 ^ 59
def prefixEnd_8157984 : Nat := 4983230072969 + 3 ^ 40 * 8157984 * 2
def baseEnd_8157984 : Nat := 4188966963688715083782121

theorem tailTrace_8157984 : CollatzResearch.WordTrace tailWord_8157984 prefixEnd_8157984 4188966963688715083782121 := by
  unfold tailWord_8157984
  simp only [CollatzResearch.WordTrace]
  refine ⟨148773060438512357794100503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198364080584683143725467337 148773060438512357794100503)
  ·
    refine ⟨223159590657768536691150755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148773060438512357794100503 223159590657768536691150755)
    ·
      refine ⟨334739385986652805036726133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223159590657768536691150755 334739385986652805036726133)
      ·
        refine ⟨31381817436248700472193075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334739385986652805036726133 31381817436248700472193075)
        ·
          refine ⟨47072726154373050708289613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31381817436248700472193075 47072726154373050708289613)
          ·
            refine ⟨17652272307889894015608605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47072726154373050708289613 17652272307889894015608605)
            ·
              refine ⟨6619602115458710255853227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17652272307889894015608605 6619602115458710255853227)
              ·
                refine ⟨9929403173188065383779841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619602115458710255853227 9929403173188065383779841)
                ·
                  refine ⟨7447052379891049037834881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9929403173188065383779841 7447052379891049037834881)
                  ·
                    refine ⟨5585289284918286778376161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7447052379891049037834881 5585289284918286778376161)
                    ·
                      refine ⟨4188966963688715083782121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585289284918286778376161 4188966963688715083782121)
                      ·
                        rfl

theorem cell23_8157984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_8157984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8157984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8157984 prefixEnd_8157984 := by exact prefixLift 8157984
  have htrace : WordTrace (prefixWord ++ tailWord_8157984) baseStart_8157984 baseEnd_8157984 := by
    simpa [prefixWord, tailWord_8157984, baseEnd_8157984] using wordTrace_append hprefix tailTrace_8157984
  have hstable : (prefixWord ++ tailWord_8157984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8157984).length < 2 ^ (prefixWord ++ tailWord_8157984).sum := by decide
  have hdescent : baseEnd_8157984 < baseStart_8157984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8157984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158026 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_8158026 : Nat := 118140960795 + 8158026 * 2 ^ 59
def prefixEnd_8158026 : Nat := 4983230072969 + 3 ^ 40 * 8158026 * 2
def baseEnd_8158026 : Nat := 4188988529876203919456927

theorem tailTrace_8158026 : CollatzResearch.WordTrace tailWord_8158026 prefixEnd_8158026 4188988529876203919456927 := by
  unfold tailWord_8158026
  simp only [CollatzResearch.WordTrace]
  refine ⟨74386913185718139190307483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198365101828581704507486621 74386913185718139190307483)
  ·
    refine ⟨111580369778577208785461225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74386913185718139190307483 111580369778577208785461225)
    ·
      refine ⟨83685277333932906589095919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111580369778577208785461225 83685277333932906589095919)
      ·
        refine ⟨125527916000899359883643879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83685277333932906589095919 125527916000899359883643879)
        ·
          refine ⟨188291874001349039825465819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125527916000899359883643879 188291874001349039825465819)
          ·
            refine ⟨282437811002023559738198729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188291874001349039825465819 282437811002023559738198729)
            ·
              refine ⟨211828358251517669803649047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282437811002023559738198729 211828358251517669803649047)
              ·
                refine ⟨317742537377276504705473571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211828358251517669803649047 317742537377276504705473571)
                ·
                  refine ⟨476613806065914757058210357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317742537377276504705473571 476613806065914757058210357)
                  ·
                    refine ⟨44682544318679508474207221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 476613806065914757058210357 44682544318679508474207221)
                    ·
                      refine ⟨4188988529876203919456927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44682544318679508474207221 4188988529876203919456927)
                      ·
                        rfl

theorem cell23_8158026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_8158026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158026 prefixEnd_8158026 := by exact prefixLift 8158026
  have htrace : WordTrace (prefixWord ++ tailWord_8158026) baseStart_8158026 baseEnd_8158026 := by
    simpa [prefixWord, tailWord_8158026, baseEnd_8158026] using wordTrace_append hprefix tailTrace_8158026
  have hstable : (prefixWord ++ tailWord_8158026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158026).length < 2 ^ (prefixWord ++ tailWord_8158026).sum := by decide
  have hdescent : baseEnd_8158026 < baseStart_8158026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158060 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_8158060 : Nat := 118140960795 + 8158060 * 2 ^ 59
def prefixEnd_8158060 : Nat := 4983230072969 + 3 ^ 40 * 8158060 * 2
def baseEnd_8158060 : Nat := 4189005988218456786431771

theorem tailTrace_8158060 : CollatzResearch.WordTrace tailWord_8158060 prefixEnd_8158060 4189005988218456786431771 := by
  unfold tailWord_8158060
  simp only [CollatzResearch.WordTrace]
  refine ⟨148774446412374690283983817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198365928549832920378645089 148774446412374690283983817)
  ·
    refine ⟨111580834809281017712987863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148774446412374690283983817 111580834809281017712987863)
    ·
      refine ⟨167371252213921526569481795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111580834809281017712987863 167371252213921526569481795)
      ·
        refine ⟨251056878320882289854222693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167371252213921526569481795 251056878320882289854222693)
        ·
          refine ⟨47073164685165429347666755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251056878320882289854222693 47073164685165429347666755)
          ·
            refine ⟨70609747027748144021500133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47073164685165429347666755 70609747027748144021500133)
            ·
              refine ⟨13239327567702777004031275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70609747027748144021500133 13239327567702777004031275)
              ·
                refine ⟨19858991351554165506046913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13239327567702777004031275 19858991351554165506046913)
                ·
                  refine ⟨14894243513665624129535185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19858991351554165506046913 14894243513665624129535185)
                  ·
                    refine ⟨11170682635249218097151389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14894243513665624129535185 11170682635249218097151389)
                    ·
                      refine ⟨4189005988218456786431771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11170682635249218097151389 4189005988218456786431771)
                      ·
                        rfl

theorem cell23_8158060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_8158060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158060 prefixEnd_8158060 := by exact prefixLift 8158060
  have htrace : WordTrace (prefixWord ++ tailWord_8158060) baseStart_8158060 baseEnd_8158060 := by
    simpa [prefixWord, tailWord_8158060, baseEnd_8158060] using wordTrace_append hprefix tailTrace_8158060
  have hstable : (prefixWord ++ tailWord_8158060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158060).length < 2 ^ (prefixWord ++ tailWord_8158060).sum := by decide
  have hdescent : baseEnd_8158060 < baseStart_8158060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158123 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 6, 4]
def baseStart_8158123 : Nat := 118140960795 + 8158123 * 2 ^ 59
def prefixEnd_8158123 : Nat := 4983230072969 + 3 ^ 40 * 8158123 * 2
def baseEnd_8158123 : Nat := 1396346112499896679981327

theorem tailTrace_8158123 : CollatzResearch.WordTrace tailWord_8158123 prefixEnd_8158123 1396346112499896679981327 := by
  unfold tailWord_8158123
  simp only [CollatzResearch.WordTrace]
  refine ⟨297551190623521142327511023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198367460415680761551674015 297551190623521142327511023)
  ·
    refine ⟨446326785935281713491266535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297551190623521142327511023 446326785935281713491266535)
    ·
      refine ⟨669490178902922570236899803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446326785935281713491266535 669490178902922570236899803)
      ·
        refine ⟨1004235268354383855355349705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669490178902922570236899803 1004235268354383855355349705)
        ·
          refine ⟨753176451265787891516512279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004235268354383855355349705 753176451265787891516512279)
          ·
            refine ⟨1129764676898681837274768419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753176451265787891516512279 1129764676898681837274768419)
            ·
              refine ⟨1694647015348022755912152629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129764676898681837274768419 1694647015348022755912152629)
              ·
                refine ⟨158873157688877133366764309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1694647015348022755912152629 158873157688877133366764309)
                ·
                  refine ⟨7447179266666115626567077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158873157688877133366764309 7447179266666115626567077)
                  ·
                    refine ⟨1396346112499896679981327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7447179266666115626567077 1396346112499896679981327)
                    ·
                      rfl

theorem cell23_8158123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 4].length) (baseStart_8158123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158123 prefixEnd_8158123 := by exact prefixLift 8158123
  have htrace : WordTrace (prefixWord ++ tailWord_8158123) baseStart_8158123 baseEnd_8158123 := by
    simpa [prefixWord, tailWord_8158123, baseEnd_8158123] using wordTrace_append hprefix tailTrace_8158123
  have hstable : (prefixWord ++ tailWord_8158123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158123).length < 2 ^ (prefixWord ++ tailWord_8158123).sum := by decide
  have hdescent : baseEnd_8158123 < baseStart_8158123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158164 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_8158164 : Nat := 118140960795 + 8158164 * 2 ^ 59
def prefixEnd_8158164 : Nat := 4983230072969 + 3 ^ 40 * 8158164 * 2
def baseEnd_8158164 : Nat := 4189059390206524379531293

theorem tailTrace_8158164 : CollatzResearch.WordTrace tailWord_8158164 prefixEnd_8158164 4189059390206524379531293 := by
  unfold tailWord_8158164
  simp only [CollatzResearch.WordTrace]
  refine ⟨148776343008186303164876773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198368457344248404219835697 148776343008186303164876773)
  ·
    refine ⟨27895564314034931843414395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148776343008186303164876773 27895564314034931843414395)
    ·
      refine ⟨41843346471052397765121593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27895564314034931843414395 41843346471052397765121593)
      ·
        refine ⟨31382509853289298323841195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41843346471052397765121593 31382509853289298323841195)
        ·
          refine ⟨47073764779933947485761793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31382509853289298323841195 47073764779933947485761793)
          ·
            refine ⟨35305323584950460614321345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47073764779933947485761793 35305323584950460614321345)
            ·
              refine ⟨26478992688712845460741009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35305323584950460614321345 26478992688712845460741009)
              ·
                refine ⟨19859244516534634095555757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26478992688712845460741009 19859244516534634095555757)
                ·
                  refine ⟨7447216693700487785833409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19859244516534634095555757 7447216693700487785833409)
                  ·
                    refine ⟨5585412520275365839375057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7447216693700487785833409 5585412520275365839375057)
                    ·
                      refine ⟨4189059390206524379531293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585412520275365839375057 4189059390206524379531293)
                      ·
                        rfl

theorem cell23_8158164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_8158164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158164 prefixEnd_8158164 := by exact prefixLift 8158164
  have htrace : WordTrace (prefixWord ++ tailWord_8158164) baseStart_8158164 baseEnd_8158164 := by
    simpa [prefixWord, tailWord_8158164, baseEnd_8158164] using wordTrace_append hprefix tailTrace_8158164
  have hstable : (prefixWord ++ tailWord_8158164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158164).length < 2 ^ (prefixWord ++ tailWord_8158164).sum := by decide
  have hdescent : baseEnd_8158164 < baseStart_8158164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158170 : List Nat := [3, 1, 1, 2, 4, 1, 4, 7]
def baseStart_8158170 : Nat := 118140960795 + 8158170 * 2 ^ 59
def prefixEnd_8158170 : Nat := 4983230072969 + 3 ^ 40 * 8158170 * 2
def baseEnd_8158170 : Nat := 155150461892238939113195

theorem tailTrace_8158170 : CollatzResearch.WordTrace tailWord_8158170 prefixEnd_8158170 155150461892238939113195 := by
  unfold tailWord_8158170
  simp only [CollatzResearch.WordTrace]
  refine ⟨74388226213587717338617991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198368603236233912902981309 74388226213587717338617991)
  ·
    refine ⟨111582339320381576007926987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74388226213587717338617991 111582339320381576007926987)
    ·
      refine ⟨167373508980572364011890481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111582339320381576007926987 167373508980572364011890481)
      ·
        refine ⟨125530131735429273008917861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167373508980572364011890481 125530131735429273008917861)
        ·
          refine ⟨23536899700392988689172099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125530131735429273008917861 23536899700392988689172099)
          ·
            refine ⟨35305349550589483033758149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23536899700392988689172099 35305349550589483033758149)
            ·
              refine ⟨6619753040735528068829653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35305349550589483033758149 6619753040735528068829653)
              ·
                refine ⟨155150461892238939113195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6619753040735528068829653 155150461892238939113195)
                ·
                  rfl

theorem cell23_8158170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_8158170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158170 prefixEnd_8158170 := by exact prefixLift 8158170
  have htrace : WordTrace (prefixWord ++ tailWord_8158170) baseStart_8158170 baseEnd_8158170 := by
    simpa [prefixWord, tailWord_8158170, baseEnd_8158170] using wordTrace_append hprefix tailTrace_8158170
  have hstable : (prefixWord ++ tailWord_8158170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158170).length < 2 ^ (prefixWord ++ tailWord_8158170).sum := by decide
  have hdescent : baseEnd_8158170 < baseStart_8158170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158203 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4]
def baseStart_8158203 : Nat := 118140960795 + 8158203 * 2 ^ 59
def prefixEnd_8158203 : Nat := 4983230072969 + 3 ^ 40 * 8158203 * 2
def baseEnd_8158203 : Nat := 4189079415952049726943613

theorem tailTrace_8158203 : CollatzResearch.WordTrace tailWord_8158203 prefixEnd_8158203 4189079415952049726943613 := by
  unfold tailWord_8158203
  simp only [CollatzResearch.WordTrace]
  refine ⟨297554108463231315990423263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198369405642154210660282175 297554108463231315990423263)
  ·
    refine ⟨446331162694846973985634895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297554108463231315990423263 446331162694846973985634895)
    ·
      refine ⟨669496744042270460978452343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446331162694846973985634895 669496744042270460978452343)
      ·
        refine ⟨1004245116063405691467678515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669496744042270460978452343 1004245116063405691467678515)
        ·
          refine ⟨1506367674095108537201517773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004245116063405691467678515 1506367674095108537201517773)
          ·
            refine ⟨564887877785665701450569165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1506367674095108537201517773 564887877785665701450569165)
            ·
              refine ⟨211832954169624638043963437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564887877785665701450569165 211832954169624638043963437)
              ·
                refine ⟨79437357813609239266486289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211832954169624638043963437 79437357813609239266486289)
                ·
                  refine ⟨59578018360206929449864717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79437357813609239266486289 59578018360206929449864717)
                  ·
                    refine ⟨22341756885077598543699269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59578018360206929449864717 22341756885077598543699269)
                    ·
                      refine ⟨4189079415952049726943613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22341756885077598543699269 4189079415952049726943613)
                      ·
                        rfl

theorem cell23_8158203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_8158203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158203 prefixEnd_8158203 := by exact prefixLift 8158203
  have htrace : WordTrace (prefixWord ++ tailWord_8158203) baseStart_8158203 baseEnd_8158203 := by
    simpa [prefixWord, tailWord_8158203, baseEnd_8158203] using wordTrace_append hprefix tailTrace_8158203
  have hstable : (prefixWord ++ tailWord_8158203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158203).length < 2 ^ (prefixWord ++ tailWord_8158203).sum := by decide
  have hdescent : baseEnd_8158203 < baseStart_8158203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158213 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_8158213 : Nat := 118140960795 + 8158213 * 2 ^ 59
def prefixEnd_8158213 : Nat := 4983230072969 + 3 ^ 40 * 8158213 * 2
def baseEnd_8158213 : Nat := 1396361516919531562606189

theorem tailTrace_8158213 : CollatzResearch.WordTrace tailWord_8158213 prefixEnd_8158213 1396361516919531562606189 := by
  unfold tailWord_8158213
  simp only [CollatzResearch.WordTrace]
  refine ⟨297554473193195087698287293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198369648795463391798858195 297554473193195087698287293)
  ·
    refine ⟨111582927447448157886857735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297554473193195087698287293 111582927447448157886857735)
    ·
      refine ⟨167374391171172236830286603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111582927447448157886857735 167374391171172236830286603)
      ·
        refine ⟨251061586756758355245429905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167374391171172236830286603 251061586756758355245429905)
        ·
          refine ⟨188296190067568766434072429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251061586756758355245429905 188296190067568766434072429)
          ·
            refine ⟨70611071275338287412777161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188296190067568766434072429 70611071275338287412777161)
            ·
              refine ⟨52958303456503715559582871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70611071275338287412777161 52958303456503715559582871)
              ·
                refine ⟨79437455184755573339374307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52958303456503715559582871 79437455184755573339374307)
                ·
                  refine ⟨119156182777133360009061461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79437455184755573339374307 119156182777133360009061461)
                  ·
                    refine ⟨1396361516919531562606189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119156182777133360009061461 1396361516919531562606189)
                    ·
                      rfl

theorem cell23_8158213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_8158213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158213 prefixEnd_8158213 := by exact prefixLift 8158213
  have htrace : WordTrace (prefixWord ++ tailWord_8158213) baseStart_8158213 baseEnd_8158213 := by
    simpa [prefixWord, tailWord_8158213, baseEnd_8158213] using wordTrace_append hprefix tailTrace_8158213
  have hstable : (prefixWord ++ tailWord_8158213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158213).length < 2 ^ (prefixWord ++ tailWord_8158213).sum := by decide
  have hdescent : baseEnd_8158213 < baseStart_8158213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158241 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_8158241 : Nat := 118140960795 + 8158241 * 2 ^ 59
def prefixEnd_8158241 : Nat := 4983230072969 + 3 ^ 40 * 8158241 * 2
def baseEnd_8158241 : Nat := 4189098928216920578268439

theorem tailTrace_8158241 : CollatzResearch.WordTrace tailWord_8158241 prefixEnd_8158241 4189098928216920578268439 := by
  unfold tailWord_8158241
  simp only [CollatzResearch.WordTrace]
  refine ⟨297555494437093648480306577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198370329624729098986871051 297555494437093648480306577)
  ·
    refine ⟨223166620827820236360229933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297555494437093648480306577 223166620827820236360229933)
    ·
      refine ⟨83687482810432588635086225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223166620827820236360229933 83687482810432588635086225)
      ·
        refine ⟨62765612107824441476314669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83687482810432588635086225 62765612107824441476314669)
        ·
          refine ⟨23537104540434165553618001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62765612107824441476314669 23537104540434165553618001)
          ·
            refine ⟨17652828405325624165213501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23537104540434165553618001 17652828405325624165213501)
            ·
              refine ⟨6619810651997109061955063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17652828405325624165213501 6619810651997109061955063)
              ·
                refine ⟨9929715977995663592932595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619810651997109061955063 9929715977995663592932595)
                ·
                  refine ⟨14894573966993495389398893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9929715977995663592932595 14894573966993495389398893)
                  ·
                    refine ⟨5585465237622560771024585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14894573966993495389398893 5585465237622560771024585)
                    ·
                      refine ⟨4189098928216920578268439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585465237622560771024585 4189098928216920578268439)
                      ·
                        rfl

theorem cell23_8158241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_8158241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158241 prefixEnd_8158241 := by exact prefixLift 8158241
  have htrace : WordTrace (prefixWord ++ tailWord_8158241) baseStart_8158241 baseEnd_8158241 := by
    simpa [prefixWord, tailWord_8158241, baseEnd_8158241] using wordTrace_append hprefix tailTrace_8158241
  have hstable : (prefixWord ++ tailWord_8158241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158241).length < 2 ^ (prefixWord ++ tailWord_8158241).sum := by decide
  have hdescent : baseEnd_8158241 < baseStart_8158241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158263 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_8158263 : Nat := 118140960795 + 8158263 * 2 ^ 59
def prefixEnd_8158263 : Nat := 4983230072969 + 3 ^ 40 * 8158263 * 2
def baseEnd_8158263 : Nat := 4189110224791319492193337

theorem tailTrace_8158263 : CollatzResearch.WordTrace tailWord_8158263 prefixEnd_8158263 4189110224791319492193337 := by
  unfold tailWord_8158263
  simp only [CollatzResearch.WordTrace]
  refine ⟨297556296843013946237607443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198370864562009297491738295 297556296843013946237607443)
  ·
    refine ⟨446334445264520919356411165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297556296843013946237607443 446334445264520919356411165)
    ·
      refine ⟨167375416974195344758654187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446334445264520919356411165 167375416974195344758654187)
      ·
        refine ⟨251063125461293017137981281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167375416974195344758654187 251063125461293017137981281)
        ·
          refine ⟨188297344095969762853485961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251063125461293017137981281 188297344095969762853485961)
          ·
            refine ⟨141223008071977322140114471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188297344095969762853485961 141223008071977322140114471)
            ·
              refine ⟨211834512107965983210171707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141223008071977322140114471 211834512107965983210171707)
              ·
                refine ⟨317751768161948974815257561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211834512107965983210171707 317751768161948974815257561)
                ·
                  refine ⟨238313826121461731111443171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317751768161948974815257561 238313826121461731111443171)
                  ·
                    refine ⟨357470739182192596667164757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238313826121461731111443171 357470739182192596667164757)
                    ·
                      refine ⟨4189110224791319492193337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357470739182192596667164757 4189110224791319492193337)
                      ·
                        rfl

theorem cell23_8158263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_8158263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158263 prefixEnd_8158263 := by exact prefixLift 8158263
  have htrace : WordTrace (prefixWord ++ tailWord_8158263) baseStart_8158263 baseEnd_8158263 := by
    simpa [prefixWord, tailWord_8158263, baseEnd_8158263] using wordTrace_append hprefix tailTrace_8158263
  have hstable : (prefixWord ++ tailWord_8158263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158263).length < 2 ^ (prefixWord ++ tailWord_8158263).sum := by decide
  have hdescent : baseEnd_8158263 < baseStart_8158263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158327 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 2, 4, 2]
def baseStart_8158327 : Nat := 118140960795 + 8158327 * 2 ^ 59
def prefixEnd_8158327 : Nat := 4983230072969 + 3 ^ 40 * 8158327 * 2
def baseEnd_8158327 : Nat := 4189143087553207241793043

theorem tailTrace_8158327 : CollatzResearch.WordTrace tailWord_8158327 prefixEnd_8158327 4189143087553207241793043 := by
  unfold tailWord_8158327
  simp only [CollatzResearch.WordTrace]
  refine ⟨297558631114782085167937235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198372420743188056778624823 297558631114782085167937235)
  ·
    refine ⟨446337946672173127751905853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297558631114782085167937235 446337946672173127751905853)
    ·
      refine ⟨167376730002064922906964695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446337946672173127751905853 167376730002064922906964695)
      ·
        refine ⟨251065095003097384360447043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167376730002064922906964695 251065095003097384360447043)
        ·
          refine ⟨376597642504646076540670565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251065095003097384360447043 376597642504646076540670565)
          ·
            refine ⟨70612057969621139351375731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376597642504646076540670565 70612057969621139351375731)
            ·
              refine ⟨105918086954431709027063597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70612057969621139351375731 105918086954431709027063597)
              ·
                refine ⟨39719282607911890885148849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105918086954431709027063597 39719282607911890885148849)
                ·
                  refine ⟨29789461955933918163861637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39719282607911890885148849 29789461955933918163861637)
                  ·
                    refine ⟨5585524116737609655724057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29789461955933918163861637 5585524116737609655724057)
                    ·
                      refine ⟨4189143087553207241793043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585524116737609655724057 4189143087553207241793043)
                      ·
                        rfl

theorem cell23_8158327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_8158327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158327 prefixEnd_8158327 := by exact prefixLift 8158327
  have htrace : WordTrace (prefixWord ++ tailWord_8158327) baseStart_8158327 baseEnd_8158327 := by
    simpa [prefixWord, tailWord_8158327, baseEnd_8158327] using wordTrace_append hprefix tailTrace_8158327
  have hstable : (prefixWord ++ tailWord_8158327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158327).length < 2 ^ (prefixWord ++ tailWord_8158327).sum := by decide
  have hdescent : baseEnd_8158327 < baseStart_8158327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158364 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_8158364 : Nat := 118140960795 + 8158364 * 2 ^ 59
def prefixEnd_8158364 : Nat := 4983230072969 + 3 ^ 40 * 8158364 * 2
def baseEnd_8158364 : Nat := 4189162086337423597030373

theorem tailTrace_8158364 : CollatzResearch.WordTrace tailWord_8158364 prefixEnd_8158364 4189162086337423597030373 := by
  unfold tailWord_8158364
  simp only [CollatzResearch.WordTrace]
  refine ⟨148779990307824020243517073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198373320410432026991356097 148779990307824020243517073)
  ·
    refine ⟨111584992730868015182637805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148779990307824020243517073 111584992730868015182637805)
    ·
      refine ⟨41844372274075505693489177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111584992730868015182637805 41844372274075505693489177)
      ·
        refine ⟨31383279205556629270116883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41844372274075505693489177 31383279205556629270116883)
        ·
          refine ⟨47074918808334943905175325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31383279205556629270116883 47074918808334943905175325)
          ·
            refine ⟨17653094553125603964440747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47074918808334943905175325 17653094553125603964440747)
            ·
              refine ⟨26479641829688405946661121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17653094553125603964440747 26479641829688405946661121)
              ·
                refine ⟨19859731372266304459995841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26479641829688405946661121 19859731372266304459995841)
                ·
                  refine ⟨14894798529199728344996881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19859731372266304459995841 14894798529199728344996881)
                  ·
                    refine ⟨11171098896899796258747661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14894798529199728344996881 11171098896899796258747661)
                    ·
                      refine ⟨4189162086337423597030373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11171098896899796258747661 4189162086337423597030373)
                      ·
                        rfl

theorem cell23_8158364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_8158364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158364 prefixEnd_8158364 := by exact prefixLift 8158364
  have htrace : WordTrace (prefixWord ++ tailWord_8158364) baseStart_8158364 baseEnd_8158364 := by
    simpa [prefixWord, tailWord_8158364, baseEnd_8158364] using wordTrace_append hprefix tailTrace_8158364
  have hstable : (prefixWord ++ tailWord_8158364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158364).length < 2 ^ (prefixWord ++ tailWord_8158364).sum := by decide
  have hdescent : baseEnd_8158364 < baseStart_8158364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158377 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 3]
def baseStart_8158377 : Nat := 118140960795 + 8158377 * 2 ^ 59
def prefixEnd_8158377 : Nat := 4983230072969 + 3 ^ 40 * 8158377 * 2
def baseEnd_8158377 : Nat := 4189168761585932046167813

theorem tailTrace_8158377 : CollatzResearch.WordTrace tailWord_8158377 prefixEnd_8158377 4189168761585932046167813 := by
  unfold tailWord_8158377
  simp only [CollatzResearch.WordTrace]
  refine ⟨297560454764600943707257385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198373636509733962471504923 297560454764600943707257385)
  ·
    refine ⟨223170341073450707780443039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297560454764600943707257385 223170341073450707780443039)
    ·
      refine ⟨334755511610176061670664559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223170341073450707780443039 334755511610176061670664559)
      ·
        refine ⟨502133267415264092505996839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334755511610176061670664559 502133267415264092505996839)
        ·
          refine ⟨753199901122896138758995259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502133267415264092505996839 753199901122896138758995259)
          ·
            refine ⟨1129799851684344208138492889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753199901122896138758995259 1129799851684344208138492889)
            ·
              refine ⟨847349888763258156103869667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129799851684344208138492889 847349888763258156103869667)
              ·
                refine ⟨1271024833144887234155804501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847349888763258156103869667 1271024833144887234155804501)
                ·
                  refine ⟨7447411131708323637631667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1271024833144887234155804501 7447411131708323637631667)
                  ·
                    refine ⟨11171116697562485456447501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7447411131708323637631667 11171116697562485456447501)
                    ·
                      refine ⟨4189168761585932046167813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11171116697562485456447501 4189168761585932046167813)
                      ·
                        rfl

theorem cell23_8158377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_8158377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158377 prefixEnd_8158377 := by exact prefixLift 8158377
  have htrace : WordTrace (prefixWord ++ tailWord_8158377) baseStart_8158377 baseEnd_8158377 := by
    simpa [prefixWord, tailWord_8158377, baseEnd_8158377] using wordTrace_append hprefix tailTrace_8158377
  have hstable : (prefixWord ++ tailWord_8158377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158377).length < 2 ^ (prefixWord ++ tailWord_8158377).sum := by decide
  have hdescent : baseEnd_8158377 < baseStart_8158377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158387 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 3, 5, 2]
def baseStart_8158387 : Nat := 118140960795 + 8158387 * 2 ^ 59
def prefixEnd_8158387 : Nat := 4983230072969 + 3 ^ 40 * 8158387 * 2
def baseEnd_8158387 : Nat := 4189173896392477007042767

theorem tailTrace_8158387 : CollatzResearch.WordTrace tailWord_8158387 prefixEnd_8158387 4189173896392477007042767 := by
  unfold tailWord_8158387
  simp only [CollatzResearch.WordTrace]
  refine ⟨297560819494564715415121415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198373879663043143610080943 297560819494564715415121415)
  ·
    refine ⟨446341229241847073122682123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297560819494564715415121415 446341229241847073122682123)
    ·
      refine ⟨669511843862770609684023185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446341229241847073122682123 669511843862770609684023185)
      ·
        refine ⟨502133882897077957263017389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669511843862770609684023185 502133882897077957263017389)
        ·
          refine ⟨188300206086404233973631521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502133882897077957263017389 188300206086404233973631521)
          ·
            refine ⟨141225154564803175480223641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188300206086404233973631521 141225154564803175480223641)
            ·
              refine ⟨105918865923602381610167731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141225154564803175480223641 105918865923602381610167731)
              ·
                refine ⟨158878298885403572415251597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105918865923602381610167731 158878298885403572415251597)
                ·
                  refine ⟨59579362082026339655719349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158878298885403572415251597 59579362082026339655719349)
                  ·
                    refine ⟨5585565195189969342723689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59579362082026339655719349 5585565195189969342723689)
                    ·
                      refine ⟨4189173896392477007042767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585565195189969342723689 4189173896392477007042767)
                      ·
                        rfl

theorem cell23_8158387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5, 2].length) (baseStart_8158387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158387 prefixEnd_8158387 := by exact prefixLift 8158387
  have htrace : WordTrace (prefixWord ++ tailWord_8158387) baseStart_8158387 baseEnd_8158387 := by
    simpa [prefixWord, tailWord_8158387, baseEnd_8158387] using wordTrace_append hprefix tailTrace_8158387
  have hstable : (prefixWord ++ tailWord_8158387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158387).length < 2 ^ (prefixWord ++ tailWord_8158387).sum := by decide
  have hdescent : baseEnd_8158387 < baseStart_8158387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158421 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_8158421 : Nat := 118140960795 + 8158421 * 2 ^ 59
def prefixEnd_8158421 : Nat := 4983230072969 + 3 ^ 40 * 8158421 * 2
def baseEnd_8158421 : Nat := 4189191354734729874017611

theorem tailTrace_8158421 : CollatzResearch.WordTrace tailWord_8158421 prefixEnd_8158421 4189191354734729874017611 := by
  unfold tailWord_8158421
  simp only [CollatzResearch.WordTrace]
  refine ⟨297562059576441539221859117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198374706384294359481239411 297562059576441539221859117)
  ·
    refine ⟨111585772341165577208197169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297562059576441539221859117 111585772341165577208197169)
    ·
      refine ⟨83689329255874182906147877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111585772341165577208197169 83689329255874182906147877)
      ·
        refine ⟨15691749235476409294902727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83689329255874182906147877 15691749235476409294902727)
        ·
          refine ⟨23537623853214613942354091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15691749235476409294902727 23537623853214613942354091)
          ·
            refine ⟨35306435779821920913531137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23537623853214613942354091 35306435779821920913531137)
            ·
              refine ⟨26479826834866440685148353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35306435779821920913531137 26479826834866440685148353)
              ·
                refine ⟨19859870126149830513861265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26479826834866440685148353 19859870126149830513861265)
                ·
                  refine ⟨14894902594612372885395949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19859870126149830513861265 14894902594612372885395949)
                  ·
                    refine ⟨5585588472979639832023481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14894902594612372885395949 5585588472979639832023481)
                    ·
                      refine ⟨4189191354734729874017611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585588472979639832023481 4189191354734729874017611)
                      ·
                        rfl

theorem cell23_8158421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_8158421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158421 prefixEnd_8158421 := by exact prefixLift 8158421
  have htrace : WordTrace (prefixWord ++ tailWord_8158421) baseStart_8158421 baseEnd_8158421 := by
    simpa [prefixWord, tailWord_8158421, baseEnd_8158421] using wordTrace_append hprefix tailTrace_8158421
  have hstable : (prefixWord ++ tailWord_8158421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158421).length < 2 ^ (prefixWord ++ tailWord_8158421).sum := by decide
  have hdescent : baseEnd_8158421 < baseStart_8158421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158422 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_8158422 : Nat := 118140960795 + 8158422 * 2 ^ 59
def prefixEnd_8158422 : Nat := 4983230072969 + 3 ^ 40 * 8158422 * 2
def baseEnd_8158422 : Nat := 1396397289405128123368369

theorem tailTrace_8158422 : CollatzResearch.WordTrace tailWord_8158422 prefixEnd_8158422 1396397289405128123368369 := by
  unfold tailWord_8158422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597631003089869774540345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198374730699625277595097013 18597631003089869774540345)
  ·
    refine ⟨13948223252317402330905259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18597631003089869774540345 13948223252317402330905259)
    ·
      refine ⟨20922334878476103496357889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13948223252317402330905259 20922334878476103496357889)
      ·
        refine ⟨15691751158857077622268417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20922334878476103496357889 15691751158857077622268417)
        ·
          refine ⟨11768813369142808216701313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15691751158857077622268417 11768813369142808216701313)
          ·
            refine ⟨8826610026857106162525985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11768813369142808216701313 8826610026857106162525985)
            ·
              refine ⟨6619957520142829621894489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8826610026857106162525985 6619957520142829621894489)
              ·
                refine ⟨4964968140107122216420867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619957520142829621894489 4964968140107122216420867)
                ·
                  refine ⟨7447452210160683324631301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964968140107122216420867 7447452210160683324631301)
                  ·
                    refine ⟨1396397289405128123368369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7447452210160683324631301 1396397289405128123368369)
                    ·
                      rfl

theorem cell23_8158422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_8158422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158422 prefixEnd_8158422 := by exact prefixLift 8158422
  have htrace : WordTrace (prefixWord ++ tailWord_8158422) baseStart_8158422 baseEnd_8158422 := by
    simpa [prefixWord, tailWord_8158422, baseEnd_8158422] using wordTrace_append hprefix tailTrace_8158422
  have hstable : (prefixWord ++ tailWord_8158422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158422).length < 2 ^ (prefixWord ++ tailWord_8158422).sum := by decide
  have hdescent : baseEnd_8158422 < baseStart_8158422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158444 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_8158444 : Nat := 118140960795 + 8158444 * 2 ^ 59
def prefixEnd_8158444 : Nat := 4983230072969 + 3 ^ 40 * 8158444 * 2
def baseEnd_8158444 : Nat := 1396401054929927761343335

theorem tailTrace_8158444 : CollatzResearch.WordTrace tailWord_8158444 prefixEnd_8158444 1396401054929927761343335 := by
  unfold tailWord_8158444
  simp only [CollatzResearch.WordTrace]
  refine ⟨148781449227679107074973193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198375265636905476099964257 148781449227679107074973193)
  ·
    refine ⟨111586086920759330306229895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148781449227679107074973193 111586086920759330306229895)
    ·
      refine ⟨167379130381138995459344843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111586086920759330306229895 167379130381138995459344843)
      ·
        refine ⟨251068695571708493189017265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167379130381138995459344843 251068695571708493189017265)
        ·
          refine ⟨188301521678781369891762949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251068695571708493189017265 188301521678781369891762949)
          ·
            refine ⟨35306535314771506854705553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188301521678781369891762949 35306535314771506854705553)
            ·
              refine ⟨26479901486078630141029165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35306535314771506854705553 26479901486078630141029165)
              ·
                refine ⟨9929963057279486302885937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26479901486078630141029165 9929963057279486302885937)
                ·
                  refine ⟨7447472292959614727164453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9929963057279486302885937 7447472292959614727164453)
                  ·
                    refine ⟨1396401054929927761343335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7447472292959614727164453 1396401054929927761343335)
                    ·
                      rfl

theorem cell23_8158444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_8158444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158444 prefixEnd_8158444 := by exact prefixLift 8158444
  have htrace : WordTrace (prefixWord ++ tailWord_8158444) baseStart_8158444 baseEnd_8158444 := by
    simpa [prefixWord, tailWord_8158444, baseEnd_8158444] using wordTrace_append hprefix tailTrace_8158444
  have hstable : (prefixWord ++ tailWord_8158444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158444).length < 2 ^ (prefixWord ++ tailWord_8158444).sum := by decide
  have hdescent : baseEnd_8158444 < baseStart_8158444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158451 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 3, 2, 2]
def baseStart_8158451 : Nat := 118140960795 + 8158451 * 2 ^ 59
def prefixEnd_8158451 : Nat := 4983230072969 + 3 ^ 40 * 8158451 * 2
def baseEnd_8158451 : Nat := 4189206759154364756642473

theorem tailTrace_8158451 : CollatzResearch.WordTrace tailWord_8158451 prefixEnd_8158451 4189206759154364756642473 := by
  unfold tailWord_8158451
  simp only [CollatzResearch.WordTrace]
  refine ⟨297563153766332854345451207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198375435844221902896967471 297563153766332854345451207)
  ·
    refine ⟨446344730649499281518176811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297563153766332854345451207 446344730649499281518176811)
    ·
      refine ⟨669517095974248922277265217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446344730649499281518176811 669517095974248922277265217)
      ·
        refine ⟨502137821980686691707948913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669517095974248922277265217 502137821980686691707948913)
        ·
          refine ⟨376603366485515018780961685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502137821980686691707948913 376603366485515018780961685)
          ·
            refine ⟨17653282804008516505357579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 376603366485515018780961685 17653282804008516505357579)
            ·
              refine ⟨26479924206012774758036369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17653282804008516505357579 26479924206012774758036369)
              ·
                refine ⟨19859943154509581068527277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26479924206012774758036369 19859943154509581068527277)
                ·
                  refine ⟨7447478682941092900697729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19859943154509581068527277 7447478682941092900697729)
                  ·
                    refine ⟨5585609012205819675523297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7447478682941092900697729 5585609012205819675523297)
                    ·
                      refine ⟨4189206759154364756642473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585609012205819675523297 4189206759154364756642473)
                      ·
                        rfl

theorem cell23_8158451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 2, 2].length) (baseStart_8158451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158451 prefixEnd_8158451 := by exact prefixLift 8158451
  have htrace : WordTrace (prefixWord ++ tailWord_8158451) baseStart_8158451 baseEnd_8158451 := by
    simpa [prefixWord, tailWord_8158451, baseEnd_8158451] using wordTrace_append hprefix tailTrace_8158451
  have hstable : (prefixWord ++ tailWord_8158451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158451).length < 2 ^ (prefixWord ++ tailWord_8158451).sum := by decide
  have hdescent : baseEnd_8158451 < baseStart_8158451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158457 : List Nat := [1, 2, 1, 3, 1, 1, 7, 7]
def baseStart_8158457 : Nat := 118140960795 + 8158457 * 2 ^ 59
def prefixEnd_8158457 : Nat := 4983230072969 + 3 ^ 40 * 8158457 * 2
def baseEnd_8158457 : Nat := 155155920001418212339535

theorem tailTrace_8158457 : CollatzResearch.WordTrace tailWord_8158457 prefixEnd_8158457 155155920001418212339535 := by
  unfold tailWord_8158457
  simp only [CollatzResearch.WordTrace]
  refine ⟨297563372604311117370169625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198375581736207411580113083 297563372604311117370169625)
  ·
    refine ⟨223172529453233338027627219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297563372604311117370169625 223172529453233338027627219)
    ·
      refine ⟨334758794179850007041440829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223172529453233338027627219 334758794179850007041440829)
      ·
        refine ⟨125534547817443752640540311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334758794179850007041440829 125534547817443752640540311)
        ·
          refine ⟨188301821726165628960810467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125534547817443752640540311 188301821726165628960810467)
          ·
            refine ⟨282452732589248443441215701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188301821726165628960810467 282452732589248443441215701)
            ·
              refine ⟨6619985920060510393153493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 282452732589248443441215701 6619985920060510393153493)
              ·
                refine ⟨155155920001418212339535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6619985920060510393153493 155155920001418212339535)
                ·
                  rfl

theorem cell23_8158457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 7].length) (baseStart_8158457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158457 prefixEnd_8158457 := by exact prefixLift 8158457
  have htrace : WordTrace (prefixWord ++ tailWord_8158457) baseStart_8158457 baseEnd_8158457 := by
    simpa [prefixWord, tailWord_8158457, baseEnd_8158457] using wordTrace_append hprefix tailTrace_8158457
  have hstable : (prefixWord ++ tailWord_8158457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158457).length < 2 ^ (prefixWord ++ tailWord_8158457).sum := by decide
  have hdescent : baseEnd_8158457 < baseStart_8158457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158468 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_8158468 : Nat := 118140960795 + 8158468 * 2 ^ 59
def prefixEnd_8158468 : Nat := 4983230072969 + 3 ^ 40 * 8158468 * 2
def baseEnd_8158468 : Nat := 4189215488325491190129895

theorem tailTrace_8158468 : CollatzResearch.WordTrace tailWord_8158468 prefixEnd_8158468 4189215488325491190129895 := by
  unfold tailWord_8158468
  simp only [CollatzResearch.WordTrace]
  refine ⟨148781886903635633124410029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198375849204847510832546705 148781886903635633124410029)
  ·
    refine ⟨55793207588863362421653761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148781886903635633124410029 55793207588863362421653761)
    ·
      refine ⟨41844905691647521816240321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55793207588863362421653761 41844905691647521816240321)
      ·
        refine ⟨31383679268735641362180241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41844905691647521816240321 31383679268735641362180241)
        ·
          refine ⟨23537759451551731021635181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31383679268735641362180241 23537759451551731021635181)
          ·
            refine ⟨8826659794331899133113193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23537759451551731021635181 8826659794331899133113193)
            ·
              refine ⟨6619994845748924349834895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8826659794331899133113193 6619994845748924349834895)
              ·
                refine ⟨9929992268623386524752343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619994845748924349834895 9929992268623386524752343)
                ·
                  refine ⟨14894988402935079787128515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9929992268623386524752343 14894988402935079787128515)
                  ·
                    refine ⟨22342482604402619680692773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14894988402935079787128515 22342482604402619680692773)
                    ·
                      refine ⟨4189215488325491190129895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22342482604402619680692773 4189215488325491190129895)
                      ·
                        rfl

theorem cell23_8158468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_8158468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158468 prefixEnd_8158468 := by exact prefixLift 8158468
  have htrace : WordTrace (prefixWord ++ tailWord_8158468) baseStart_8158468 baseEnd_8158468 := by
    simpa [prefixWord, tailWord_8158468, baseEnd_8158468] using wordTrace_append hprefix tailTrace_8158468
  have hstable : (prefixWord ++ tailWord_8158468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158468).length < 2 ^ (prefixWord ++ tailWord_8158468).sum := by decide
  have hdescent : baseEnd_8158468 < baseStart_8158468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158498 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_8158498 : Nat := 118140960795 + 8158498 * 2 ^ 59
def prefixEnd_8158498 : Nat := 4983230072969 + 3 ^ 40 * 8158498 * 2
def baseEnd_8158498 : Nat := 4189230892745126072754757

theorem tailTrace_8158498 : CollatzResearch.WordTrace tailWord_8158498 prefixEnd_8158498 4189230892745126072754757 := by
  unfold tailWord_8158498
  simp only [CollatzResearch.WordTrace]
  refine ⟨74391216999290645343103037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198376578664775054248274765 74391216999290645343103037)
  ·
    refine ⟨27896706374733992003663639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74391216999290645343103037 27896706374733992003663639)
    ·
      refine ⟨41845059562100988005495459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27896706374733992003663639 41845059562100988005495459)
      ·
        refine ⟨62767589343151482008243189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41845059562100988005495459 62767589343151482008243189)
        ·
          refine ⟨5884461500920451438272799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62767589343151482008243189 5884461500920451438272799)
          ·
            refine ⟨8826692251380677157409199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884461500920451438272799 8826692251380677157409199)
            ·
              refine ⟨13240038377071015736113799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8826692251380677157409199 13240038377071015736113799)
              ·
                refine ⟨19860057565606523604170699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240038377071015736113799 19860057565606523604170699)
                ·
                  refine ⟨29790086348409785406256049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19860057565606523604170699 29790086348409785406256049)
                  ·
                    refine ⟨22342564761307339054692037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29790086348409785406256049 22342564761307339054692037)
                    ·
                      refine ⟨4189230892745126072754757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22342564761307339054692037 4189230892745126072754757)
                      ·
                        rfl

theorem cell23_8158498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_8158498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158498 prefixEnd_8158498 := by exact prefixLift 8158498
  have htrace : WordTrace (prefixWord ++ tailWord_8158498) baseStart_8158498 baseEnd_8158498 := by
    simpa [prefixWord, tailWord_8158498, baseEnd_8158498] using wordTrace_append hprefix tailTrace_8158498
  have hstable : (prefixWord ++ tailWord_8158498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158498).length < 2 ^ (prefixWord ++ tailWord_8158498).sum := by decide
  have hdescent : baseEnd_8158498 < baseStart_8158498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158501 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_8158501 : Nat := 118140960795 + 8158501 * 2 ^ 59
def prefixEnd_8158501 : Nat := 4983230072969 + 3 ^ 40 * 8158501 * 2
def baseEnd_8158501 : Nat := 4189232433187089561017243

theorem tailTrace_8158501 : CollatzResearch.WordTrace tailWord_8158501 prefixEnd_8158501 4189232433187089561017243 := by
  unfold tailWord_8158501
  simp only [CollatzResearch.WordTrace]
  refine ⟨297564977416151712884771357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198376651610767808589847571 297564977416151712884771357)
  ·
    refine ⟨111586866531056892331789259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297564977416151712884771357 111586866531056892331789259)
    ·
      refine ⟨167380299796585338497683889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111586866531056892331789259 167380299796585338497683889)
      ·
        refine ⟨125535224847439003873262917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167380299796585338497683889 125535224847439003873262917)
        ·
          refine ⟨23537854658894813226236797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125535224847439003873262917 23537854658894813226236797)
          ·
            refine ⟨8826695497085554959838799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23537854658894813226236797 8826695497085554959838799)
            ·
              refine ⟨13240043245628332439758199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8826695497085554959838799 13240043245628332439758199)
              ·
                refine ⟨19860064868442498659637299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240043245628332439758199 19860064868442498659637299)
                ·
                  refine ⟨29790097302663747989455949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19860064868442498659637299 29790097302663747989455949)
                  ·
                    refine ⟨11171286488498905496045981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29790097302663747989455949 11171286488498905496045981)
                    ·
                      refine ⟨4189232433187089561017243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11171286488498905496045981 4189232433187089561017243)
                      ·
                        rfl

theorem cell23_8158501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_8158501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158501 prefixEnd_8158501 := by exact prefixLift 8158501
  have htrace : WordTrace (prefixWord ++ tailWord_8158501) baseStart_8158501 baseEnd_8158501 := by
    simpa [prefixWord, tailWord_8158501, baseEnd_8158501] using wordTrace_append hprefix tailTrace_8158501
  have hstable : (prefixWord ++ tailWord_8158501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158501).length < 2 ^ (prefixWord ++ tailWord_8158501).sum := by decide
  have hdescent : baseEnd_8158501 < baseStart_8158501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158527 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_8158527 : Nat := 118140960795 + 8158527 * 2 ^ 59
def prefixEnd_8158527 : Nat := 4983230072969 + 3 ^ 40 * 8158527 * 2
def baseEnd_8158527 : Nat := 4189245783684106459292123

theorem tailTrace_8158527 : CollatzResearch.WordTrace tailWord_8158527 prefixEnd_8158527 4189245783684106459292123 := by
  unfold tailWord_8158527
  simp only [CollatzResearch.WordTrace]
  refine ⟨297565925714057519325217835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198377283809371679550145223 297565925714057519325217835)
  ·
    refine ⟨446348888571086278987826753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297565925714057519325217835 446348888571086278987826753)
    ·
      refine ⟨334761666428314709240870065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446348888571086278987826753 334761666428314709240870065)
      ·
        refine ⟨251071249821236031930652549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334761666428314709240870065 251071249821236031930652549)
        ·
          refine ⟨47075859341481755986997353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251071249821236031930652549 47075859341481755986997353)
          ·
            refine ⟨35306894506111316990248015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47075859341481755986997353 35306894506111316990248015)
            ·
              refine ⟨52960341759166975485372023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35306894506111316990248015 52960341759166975485372023)
              ·
                refine ⟨79440512638750463228058035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52960341759166975485372023 79440512638750463228058035)
                ·
                  refine ⟨119160768958125694842087053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79440512638750463228058035 119160768958125694842087053)
                  ·
                    refine ⟨44685288359297135565782645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119160768958125694842087053 44685288359297135565782645)
                    ·
                      refine ⟨4189245783684106459292123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44685288359297135565782645 4189245783684106459292123)
                      ·
                        rfl

theorem cell23_8158527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_8158527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158527 prefixEnd_8158527 := by exact prefixLift 8158527
  have htrace : WordTrace (prefixWord ++ tailWord_8158527) baseStart_8158527 baseEnd_8158527 := by
    simpa [prefixWord, tailWord_8158527, baseEnd_8158527] using wordTrace_append hprefix tailTrace_8158527
  have hstable : (prefixWord ++ tailWord_8158527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158527).length < 2 ^ (prefixWord ++ tailWord_8158527).sum := by decide
  have hdescent : baseEnd_8158527 < baseStart_8158527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158537 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_8158537 : Nat := 118140960795 + 8158537 * 2 ^ 59
def prefixEnd_8158537 : Nat := 4983230072969 + 3 ^ 40 * 8158537 * 2
def baseEnd_8158537 : Nat := 4189250918490651420167077

theorem tailTrace_8158537 : CollatzResearch.WordTrace tailWord_8158537 prefixEnd_8158537 4189250918490651420167077 := by
  unfold tailWord_8158537
  simp only [CollatzResearch.WordTrace]
  refine ⟨297566290444021291033081865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198377526962680860688721243 297566290444021291033081865)
  ·
    refine ⟨223174717833015968274811399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297566290444021291033081865 223174717833015968274811399)
    ·
      refine ⟨334762076749523952412217099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223174717833015968274811399 334762076749523952412217099)
      ·
        refine ⟨502143115124285928618325649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334762076749523952412217099 502143115124285928618325649)
        ·
          refine ⟨376607336343214446463744237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502143115124285928618325649 376607336343214446463744237)
          ·
            refine ⟨141227751128705417423904089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376607336343214446463744237 141227751128705417423904089)
            ·
              refine ⟨105920813346529063067928067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141227751128705417423904089 105920813346529063067928067)
              ·
                refine ⟨158881220019793594601892101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105920813346529063067928067 158881220019793594601892101)
                ·
                  refine ⟨29790228753711298987854769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158881220019793594601892101 29790228753711298987854769)
                  ·
                    refine ⟨22342671565283474240891077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29790228753711298987854769 22342671565283474240891077)
                    ·
                      refine ⟨4189250918490651420167077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22342671565283474240891077 4189250918490651420167077)
                      ·
                        rfl

theorem cell23_8158537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_8158537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158537 prefixEnd_8158537 := by exact prefixLift 8158537
  have htrace : WordTrace (prefixWord ++ tailWord_8158537) baseStart_8158537 baseEnd_8158537 := by
    simpa [prefixWord, tailWord_8158537, baseEnd_8158537] using wordTrace_append hprefix tailTrace_8158537
  have hstable : (prefixWord ++ tailWord_8158537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158537).length < 2 ^ (prefixWord ++ tailWord_8158537).sum := by decide
  have hdescent : baseEnd_8158537 < baseStart_8158537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158577 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_8158577 : Nat := 118140960795 + 8158577 * 2 ^ 59
def prefixEnd_8158577 : Nat := 4983230072969 + 3 ^ 40 * 8158577 * 2
def baseEnd_8158577 : Nat := 1396423819238943754555631

theorem tailTrace_8158577 : CollatzResearch.WordTrace tailWord_8158577 prefixEnd_8158577 1396423819238943754555631 := by
  unfold tailWord_8158577
  simp only [CollatzResearch.WordTrace]
  refine ⟨297567749363876377864537985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198378499575917585243025323 297567749363876377864537985)
  ·
    refine ⟨223175812022907283398403489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297567749363876377864537985 223175812022907283398403489)
    ·
      refine ⟨167381859017180462548802617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223175812022907283398403489 167381859017180462548802617)
      ·
        refine ⟨125536394262885346911601963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167381859017180462548802617 125536394262885346911601963)
        ·
          refine ⟨188304591394328020367402945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125536394262885346911601963 188304591394328020367402945)
          ·
            refine ⟨141228443545746015275552209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188304591394328020367402945 141228443545746015275552209)
            ·
              refine ⟨105921332659309511456664157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141228443545746015275552209 105921332659309511456664157)
              ·
                refine ⟨39720499747241066796249059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105921332659309511456664157 39720499747241066796249059)
                ·
                  refine ⟨59580749620861600194373589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39720499747241066796249059 59580749620861600194373589)
                  ·
                    refine ⟨1396423819238943754555631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59580749620861600194373589 1396423819238943754555631)
                    ·
                      rfl

theorem cell23_8158577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_8158577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158577 prefixEnd_8158577 := by exact prefixLift 8158577
  have htrace : WordTrace (prefixWord ++ tailWord_8158577) baseStart_8158577 baseEnd_8158577 := by
    simpa [prefixWord, tailWord_8158577, baseEnd_8158577] using wordTrace_append hprefix tailTrace_8158577
  have hstable : (prefixWord ++ tailWord_8158577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158577).length < 2 ^ (prefixWord ++ tailWord_8158577).sum := by decide
  have hdescent : baseEnd_8158577 < baseStart_8158577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158584 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 6, 5, 2]
def baseStart_8158584 : Nat := 118140960795 + 8158584 * 2 ^ 59
def prefixEnd_8158584 : Nat := 4983230072969 + 3 ^ 40 * 8158584 * 2
def baseEnd_8158584 : Nat := 4189275052081412736279361

theorem tailTrace_8158584 : CollatzResearch.WordTrace tailWord_8158584 prefixEnd_8158584 4189275052081412736279361 := by
  unfold tailWord_8158584
  simp only [CollatzResearch.WordTrace]
  refine ⟨148784002337425509030021403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198378669783234012040028537 148784002337425509030021403)
  ·
    refine ⟨223176003506138263545032105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148784002337425509030021403 223176003506138263545032105)
    ·
      refine ⟨167382002629603697658774079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223176003506138263545032105 167382002629603697658774079)
      ·
        refine ⟨251073003944405546488161119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167382002629603697658774079 251073003944405546488161119)
        ·
          refine ⟨376609505916608319732241679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251073003944405546488161119 376609505916608319732241679)
          ·
            refine ⟨564914258874912479598362519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376609505916608319732241679 564914258874912479598362519)
            ·
              refine ⟨847371388312368719397543779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564914258874912479598362519 847371388312368719397543779)
              ·
                refine ⟨1271057082468553079096315669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847371388312368719397543779 1271057082468553079096315669)
                ·
                  refine ⟨59580800740713425582639797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1271057082468553079096315669 59580800740713425582639797)
                  ·
                    refine ⟨5585700069441883648372481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59580800740713425582639797 5585700069441883648372481)
                    ·
                      refine ⟨4189275052081412736279361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585700069441883648372481 4189275052081412736279361)
                      ·
                        rfl

theorem cell23_8158584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_8158584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158584 prefixEnd_8158584 := by exact prefixLift 8158584
  have htrace : WordTrace (prefixWord ++ tailWord_8158584) baseStart_8158584 baseEnd_8158584 := by
    simpa [prefixWord, tailWord_8158584, baseEnd_8158584] using wordTrace_append hprefix tailTrace_8158584
  have hstable : (prefixWord ++ tailWord_8158584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158584).length < 2 ^ (prefixWord ++ tailWord_8158584).sum := by decide
  have hdescent : baseEnd_8158584 < baseStart_8158584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158587 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_8158587 : Nat := 118140960795 + 8158587 * 2 ^ 59
def prefixEnd_8158587 : Nat := 4983230072969 + 3 ^ 40 * 8158587 * 2
def baseEnd_8158587 : Nat := 4189276592523376224541847

theorem tailTrace_8158587 : CollatzResearch.WordTrace tailWord_8158587 prefixEnd_8158587 4189276592523376224541847 := by
  unfold tailWord_8158587
  simp only [CollatzResearch.WordTrace]
  refine ⟨297568114093840149572402015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198378742729226766381601343 297568114093840149572402015)
  ·
    refine ⟨446352171140760224358603023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297568114093840149572402015 446352171140760224358603023)
    ·
      refine ⟨669528256711140336537904535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446352171140760224358603023 669528256711140336537904535)
      ·
        refine ⟨1004292385066710504806856803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669528256711140336537904535 1004292385066710504806856803)
        ·
          refine ⟨1506438577600065757210285205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004292385066710504806856803 1506438577600065757210285205)
          ·
            refine ⟨70614308325003082369232119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1506438577600065757210285205 70614308325003082369232119)
            ·
              refine ⟨105921462487504623553848179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70614308325003082369232119 105921462487504623553848179)
              ·
                refine ⟨158882193731256935330772269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105921462487504623553848179 158882193731256935330772269)
                ·
                  refine ⟨59580822649221350749039601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158882193731256935330772269 59580822649221350749039601)
                  ·
                    refine ⟨44685616986916013061779701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59580822649221350749039601 44685616986916013061779701)
                    ·
                      refine ⟨4189276592523376224541847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44685616986916013061779701 4189276592523376224541847)
                      ·
                        rfl

theorem cell23_8158587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_8158587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158587 prefixEnd_8158587 := by exact prefixLift 8158587
  have htrace : WordTrace (prefixWord ++ tailWord_8158587) baseStart_8158587 baseEnd_8158587 := by
    simpa [prefixWord, tailWord_8158587, baseEnd_8158587] using wordTrace_append hprefix tailTrace_8158587
  have hstable : (prefixWord ++ tailWord_8158587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158587).length < 2 ^ (prefixWord ++ tailWord_8158587).sum := by decide
  have hdescent : baseEnd_8158587 < baseStart_8158587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158631 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_8158631 : Nat := 118140960795 + 8158631 * 2 ^ 59
def prefixEnd_8158631 : Nat := 4983230072969 + 3 ^ 40 * 8158631 * 2
def baseEnd_8158631 : Nat := 4189299185672174052391645

theorem tailTrace_8158631 : CollatzResearch.WordTrace tailWord_8158631 prefixEnd_8158631 4189299185672174052391645 := by
  unfold tailWord_8158631
  simp only [CollatzResearch.WordTrace]
  refine ⟨297569718905680745087003747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198379812603787163391335831 297569718905680745087003747)
  ·
    refine ⟨446354578358521117630505621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297569718905680745087003747 446354578358521117630505621)
    ·
      refine ⟨20922870860555677388929951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 446354578358521117630505621 20922870860555677388929951)
      ·
        refine ⟨31384306290833516083394927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20922870860555677388929951 31384306290833516083394927)
        ·
          refine ⟨47076459436250274125092391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31384306290833516083394927 47076459436250274125092391)
          ·
            refine ⟨70614689154375411187638587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47076459436250274125092391 70614689154375411187638587)
            ·
              refine ⟨105922033731563116781457881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70614689154375411187638587 105922033731563116781457881)
              ·
                refine ⟨79441525298672337586093411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105922033731563116781457881 79441525298672337586093411)
                ·
                  refine ⟨119162287948008506379140117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79441525298672337586093411 119162287948008506379140117)
                  ·
                    refine ⟨5585732247562898736522193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119162287948008506379140117 5585732247562898736522193)
                    ·
                      refine ⟨4189299185672174052391645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585732247562898736522193 4189299185672174052391645)
                      ·
                        rfl

theorem cell23_8158631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_8158631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158631 prefixEnd_8158631 := by exact prefixLift 8158631
  have htrace : WordTrace (prefixWord ++ tailWord_8158631) baseStart_8158631 baseEnd_8158631 := by
    simpa [prefixWord, tailWord_8158631, baseEnd_8158631] using wordTrace_append hprefix tailTrace_8158631
  have hstable : (prefixWord ++ tailWord_8158631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158631).length < 2 ^ (prefixWord ++ tailWord_8158631).sum := by decide
  have hdescent : baseEnd_8158631 < baseStart_8158631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158755 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 1, 1, 4]
def baseStart_8158755 : Nat := 118140960795 + 8158755 * 2 ^ 59
def prefixEnd_8158755 : Nat := 4983230072969 + 3 ^ 40 * 8158755 * 2
def baseEnd_8158755 : Nat := 4189362857273331567241075

theorem tailTrace_8158755 : CollatzResearch.WordTrace tailWord_8158755 prefixEnd_8158755 4189362857273331567241075 := by
  unfold tailWord_8158755
  simp only [CollatzResearch.WordTrace]
  refine ⟨297574241557231514264517719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198382827704821009509678479 297574241557231514264517719)
  ·
    refine ⟨446361362335847271396776579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297574241557231514264517719 446361362335847271396776579)
    ·
      refine ⟨669542043503770907095164869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446361362335847271396776579 669542043503770907095164869)
      ·
        refine ⟨125539133156957045080343413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 669542043503770907095164869 125539133156957045080343413)
        ·
          refine ⟨11769293733464722976282195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125539133156957045080343413 11769293733464722976282195)
          ·
            refine ⟨17653940600197084464423293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769293733464722976282195 17653940600197084464423293)
            ·
              refine ⟨6620227725073906674158735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17653940600197084464423293 6620227725073906674158735)
              ·
                refine ⟨9930341587610860011238103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620227725073906674158735 9930341587610860011238103)
                ·
                  refine ⟨14895512381416290016857155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9930341587610860011238103 14895512381416290016857155)
                  ·
                    refine ⟨22343268572124435025285733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14895512381416290016857155 22343268572124435025285733)
                    ·
                      refine ⟨4189362857273331567241075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22343268572124435025285733 4189362857273331567241075)
                      ·
                        rfl

theorem cell23_8158755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_8158755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158755 prefixEnd_8158755 := by exact prefixLift 8158755
  have htrace : WordTrace (prefixWord ++ tailWord_8158755) baseStart_8158755 baseEnd_8158755 := by
    simpa [prefixWord, tailWord_8158755, baseEnd_8158755] using wordTrace_append hprefix tailTrace_8158755
  have hstable : (prefixWord ++ tailWord_8158755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158755).length < 2 ^ (prefixWord ++ tailWord_8158755).sum := by decide
  have hdescent : baseEnd_8158755 < baseStart_8158755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158784 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_8158784 : Nat := 118140960795 + 8158784 * 2 ^ 59
def prefixEnd_8158784 : Nat := 4983230072969 + 3 ^ 40 * 8158784 * 2
def baseEnd_8158784 : Nat := 4189377748212311953778441

theorem tailTrace_8158784 : CollatzResearch.WordTrace tailWord_8158784 prefixEnd_8158784 4189377748212311953778441 := by
  unfold tailWord_8158784
  simp only [CollatzResearch.WordTrace]
  refine ⟨148787649637063226108661703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198383532849417634811548937 148787649637063226108661703)
  ·
    refine ⟨223181474455594839162992555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148787649637063226108661703 223181474455594839162992555)
    ·
      refine ⟨334772211683392258744488833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223181474455594839162992555 334772211683392258744488833)
      ·
        refine ⟨251079158762544194058366625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334772211683392258744488833 251079158762544194058366625)
        ·
          refine ⟨188309369071908145543774969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251079158762544194058366625 188309369071908145543774969)
          ·
            refine ⟨141232026803931109157831227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188309369071908145543774969 141232026803931109157831227)
            ·
              refine ⟨211848040205896663736746841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141232026803931109157831227 211848040205896663736746841)
              ·
                refine ⟨158886030154422497802560131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211848040205896663736746841 158886030154422497802560131)
                ·
                  refine ⟨238329045231633746703840197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158886030154422497802560131 238329045231633746703840197)
                  ·
                    refine ⟨44686695980931327506970037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238329045231633746703840197 44686695980931327506970037)
                    ·
                      refine ⟨4189377748212311953778441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44686695980931327506970037 4189377748212311953778441)
                      ·
                        rfl

theorem cell23_8158784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_8158784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158784 prefixEnd_8158784 := by exact prefixLift 8158784
  have htrace : WordTrace (prefixWord ++ tailWord_8158784) baseStart_8158784 baseEnd_8158784 := by
    simpa [prefixWord, tailWord_8158784, baseEnd_8158784] using wordTrace_append hprefix tailTrace_8158784
  have hstable : (prefixWord ++ tailWord_8158784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158784).length < 2 ^ (prefixWord ++ tailWord_8158784).sum := by decide
  have hdescent : baseEnd_8158784 < baseStart_8158784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158806 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_8158806 : Nat := 118140960795 + 8158806 * 2 ^ 59
def prefixEnd_8158806 : Nat := 4983230072969 + 3 ^ 40 * 8158806 * 2
def baseEnd_8158806 : Nat := 4189389044786710867703341

theorem tailTrace_8158806 : CollatzResearch.WordTrace tailWord_8158806 prefixEnd_8158806 4189389044786710867703341 := by
  unfold tailWord_8158806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598506355002921873414017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198384067786697833316416181 18598506355002921873414017)
  ·
    refine ⟨13948879766252191405060513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18598506355002921873414017 13948879766252191405060513)
    ·
      refine ⟨10461659824689143553795385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13948879766252191405060513 10461659824689143553795385)
      ·
        refine ⟨7846244868516857665346539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10461659824689143553795385 7846244868516857665346539)
        ·
          refine ⟨11769367302775286498019809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846244868516857665346539 11769367302775286498019809)
          ·
            refine ⟨8827025477081464873514857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11769367302775286498019809 8827025477081464873514857)
            ·
              refine ⟨6620269107811098655136143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8827025477081464873514857 6620269107811098655136143)
              ·
                refine ⟨9930403661716647982704215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620269107811098655136143 9930403661716647982704215)
                ·
                  refine ⟨14895605492574971974056323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9930403661716647982704215 14895605492574971974056323)
                  ·
                    refine ⟨22343408238862457961084485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14895605492574971974056323 22343408238862457961084485)
                    ·
                      refine ⟨4189389044786710867703341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22343408238862457961084485 4189389044786710867703341)
                      ·
                        rfl

theorem cell23_8158806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_8158806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158806 prefixEnd_8158806 := by exact prefixLift 8158806
  have htrace : WordTrace (prefixWord ++ tailWord_8158806) baseStart_8158806 baseEnd_8158806 := by
    simpa [prefixWord, tailWord_8158806, baseEnd_8158806] using wordTrace_append hprefix tailTrace_8158806
  have hstable : (prefixWord ++ tailWord_8158806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158806).length < 2 ^ (prefixWord ++ tailWord_8158806).sum := by decide
  have hdescent : baseEnd_8158806 < baseStart_8158806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158821 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_8158821 : Nat := 118140960795 + 8158821 * 2 ^ 59
def prefixEnd_8158821 : Nat := 4983230072969 + 3 ^ 40 * 8158821 * 2
def baseEnd_8158821 : Nat := 1396465582332176103005257

theorem tailTrace_8158821 : CollatzResearch.WordTrace tailWord_8158821 prefixEnd_8158821 1396465582332176103005257 := by
  unfold tailWord_8158821
  simp only [CollatzResearch.WordTrace]
  refine ⟨297576648774992407536420317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198384432516661605024280211 297576648774992407536420317)
  ·
    refine ⟨111591243290622152826157619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297576648774992407536420317 111591243290622152826157619)
    ·
      refine ⟨167386864935933229239236429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111591243290622152826157619 167386864935933229239236429)
      ·
        refine ⟨62770074350974960964713661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167386864935933229239236429 62770074350974960964713661)
        ·
          refine ⟨23538777881615610361767623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62770074350974960964713661 23538777881615610361767623)
          ·
            refine ⟨35308166822423415542651435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23538777881615610361767623 35308166822423415542651435)
            ·
              refine ⟨52962250233635123313977153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35308166822423415542651435 52962250233635123313977153)
              ·
                refine ⟨39721687675226342485482865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52962250233635123313977153 39721687675226342485482865)
                ·
                  refine ⟨29791265756419756864112149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39721687675226342485482865 29791265756419756864112149)
                  ·
                    refine ⟨1396465582332176103005257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29791265756419756864112149 1396465582332176103005257)
                    ·
                      rfl

theorem cell23_8158821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_8158821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158821 prefixEnd_8158821 := by exact prefixLift 8158821
  have htrace : WordTrace (prefixWord ++ tailWord_8158821) baseStart_8158821 baseEnd_8158821 := by
    simpa [prefixWord, tailWord_8158821, baseEnd_8158821] using wordTrace_append hprefix tailTrace_8158821
  have hstable : (prefixWord ++ tailWord_8158821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158821).length < 2 ^ (prefixWord ++ tailWord_8158821).sum := by decide
  have hdescent : baseEnd_8158821 < baseStart_8158821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158838 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_8158838 : Nat := 118140960795 + 8158838 * 2 ^ 59
def prefixEnd_8158838 : Nat := 4983230072969 + 3 ^ 40 * 8158838 * 2
def baseEnd_8158838 : Nat := 1396468492055884914167731

theorem tailTrace_8158838 : CollatzResearch.WordTrace tailWord_8158838 prefixEnd_8158838 1396468492055884914167731 := by
  unfold tailWord_8158838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598579300995676214986823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198384845877287212959859445 18598579300995676214986823)
  ·
    refine ⟨27897868951493514322480235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598579300995676214986823 27897868951493514322480235)
    ·
      refine ⟨41846803427240271483720353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27897868951493514322480235 41846803427240271483720353)
      ·
        refine ⟨31385102570430203612790265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41846803427240271483720353 31385102570430203612790265)
        ·
          refine ⟨23538826927822652709592699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31385102570430203612790265 23538826927822652709592699)
          ·
            refine ⟨35308240391733979064389049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23538826927822652709592699 35308240391733979064389049)
            ·
              refine ⟨26481180293800484298291787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35308240391733979064389049 26481180293800484298291787)
              ·
                refine ⟨39721770440700726447437681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26481180293800484298291787 39721770440700726447437681)
                ·
                  refine ⟨29791327830525544835578261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39721770440700726447437681 29791327830525544835578261)
                  ·
                    refine ⟨1396468492055884914167731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29791327830525544835578261 1396468492055884914167731)
                    ·
                      rfl

theorem cell23_8158838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_8158838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158838 prefixEnd_8158838 := by exact prefixLift 8158838
  have htrace : WordTrace (prefixWord ++ tailWord_8158838) baseStart_8158838 baseEnd_8158838 := by
    simpa [prefixWord, tailWord_8158838, baseEnd_8158838] using wordTrace_append hprefix tailTrace_8158838
  have hstable : (prefixWord ++ tailWord_8158838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158838).length < 2 ^ (prefixWord ++ tailWord_8158838).sum := by decide
  have hdescent : baseEnd_8158838 < baseStart_8158838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158841 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_8158841 : Nat := 118140960795 + 8158841 * 2 ^ 59
def prefixEnd_8158841 : Nat := 4983230072969 + 3 ^ 40 * 8158841 * 2
def baseEnd_8158841 : Nat := 4189407016609618230765679

theorem tailTrace_8158841 : CollatzResearch.WordTrace tailWord_8158841 prefixEnd_8158841 4189407016609618230765679 := by
  unfold tailWord_8158841
  simp only [CollatzResearch.WordTrace]
  refine ⟨297577378234919950952148377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198384918823279967301432251 297577378234919950952148377)
  ·
    refine ⟨223183033676189963214111283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297577378234919950952148377 223183033676189963214111283)
    ·
      refine ⟨334774550514284944821166925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223183033676189963214111283 334774550514284944821166925)
      ·
        refine ⟨125540456442856854307937597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334774550514284944821166925 125540456442856854307937597)
        ·
          refine ⟨47077671166071320365476599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125540456442856854307937597 47077671166071320365476599)
          ·
            refine ⟨70616506749106980548214899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47077671166071320365476599 70616506749106980548214899)
            ·
              refine ⟨105924760123660470822322349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70616506749106980548214899 105924760123660470822322349)
              ·
                refine ⟨39721785046372676558370881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105924760123660470822322349 39721785046372676558370881)
                ·
                  refine ⟨29791338784779507418778161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39721785046372676558370881 29791338784779507418778161)
                  ·
                    refine ⟨22343504088584630564083621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29791338784779507418778161 22343504088584630564083621)
                    ·
                      refine ⟨4189407016609618230765679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22343504088584630564083621 4189407016609618230765679)
                      ·
                        rfl

theorem cell23_8158841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_8158841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158841 prefixEnd_8158841 := by exact prefixLift 8158841
  have htrace : WordTrace (prefixWord ++ tailWord_8158841) baseStart_8158841 baseEnd_8158841 := by
    simpa [prefixWord, tailWord_8158841, baseEnd_8158841] using wordTrace_append hprefix tailTrace_8158841
  have hstable : (prefixWord ++ tailWord_8158841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158841).length < 2 ^ (prefixWord ++ tailWord_8158841).sum := by decide
  have hdescent : baseEnd_8158841 < baseStart_8158841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158845 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_8158845 : Nat := 118140960795 + 8158845 * 2 ^ 59
def prefixEnd_8158845 : Nat := 4983230072969 + 3 ^ 40 * 8158845 * 2
def baseEnd_8158845 : Nat := 4189409070532236215115661

theorem tailTrace_8158845 : CollatzResearch.WordTrace tailWord_8158845 prefixEnd_8158845 4189409070532236215115661 := by
  unfold tailWord_8158845
  simp only [CollatzResearch.WordTrace]
  refine ⟨297577524126905459635293989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198385016084603639756862659 297577524126905459635293989)
  ·
    refine ⟨55795785773794773681617623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297577524126905459635293989 55795785773794773681617623)
    ·
      refine ⟨83693678660692160522426435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55795785773794773681617623 83693678660692160522426435)
      ·
        refine ⟨125540517991038240783639653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83693678660692160522426435 125540517991038240783639653)
        ·
          refine ⟨23538847123319670146932435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125540517991038240783639653 23538847123319670146932435)
          ·
            refine ⟨35308270684979505220398653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23538847123319670146932435 35308270684979505220398653)
            ·
              refine ⟨13240601506867314457649495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35308270684979505220398653 13240601506867314457649495)
              ·
                refine ⟨19860902260300971686474243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240601506867314457649495 19860902260300971686474243)
                ·
                  refine ⟨29791353390451457529711365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19860902260300971686474243 29791353390451457529711365)
                  ·
                    refine ⟨5585878760709648286820881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29791353390451457529711365 5585878760709648286820881)
                    ·
                      refine ⟨4189409070532236215115661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5585878760709648286820881 4189409070532236215115661)
                      ·
                        rfl

theorem cell23_8158845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_8158845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158845 prefixEnd_8158845 := by exact prefixLift 8158845
  have htrace : WordTrace (prefixWord ++ tailWord_8158845) baseStart_8158845 baseEnd_8158845 := by
    simpa [prefixWord, tailWord_8158845, baseEnd_8158845] using wordTrace_append hprefix tailTrace_8158845
  have hstable : (prefixWord ++ tailWord_8158845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158845).length < 2 ^ (prefixWord ++ tailWord_8158845).sum := by decide
  have hdescent : baseEnd_8158845 < baseStart_8158845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158925 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_8158925 : Nat := 118140960795 + 8158925 * 2 ^ 59
def prefixEnd_8158925 : Nat := 4983230072969 + 3 ^ 40 * 8158925 * 2
def baseEnd_8158925 : Nat := 4189450148984595902115293

theorem tailTrace_8158925 : CollatzResearch.WordTrace tailWord_8158925 prefixEnd_8158925 4189450148984595902115293 := by
  unfold tailWord_8158925
  simp only [CollatzResearch.WordTrace]
  refine ⟨297580441966615633298206229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198386961311077088865470819 297580441966615633298206229)
  ·
    refine ⟨13949083217185107810853417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297580441966615633298206229 13949083217185107810853417)
    ·
      refine ⟨10461812412888830858140063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13949083217185107810853417 10461812412888830858140063)
      ·
        refine ⟨15692718619333246287210095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10461812412888830858140063 15692718619333246287210095)
        ·
          refine ⟨23539077928999869430815143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15692718619333246287210095 23539077928999869430815143)
          ·
            refine ⟨35308616893499804146222715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23539077928999869430815143 35308616893499804146222715)
            ·
              refine ⟨52962925340249706219334073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35308616893499804146222715 52962925340249706219334073)
              ·
                refine ⟨39722194005187279664500555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52962925340249706219334073 39722194005187279664500555)
                ·
                  refine ⟨59583291007780919496750833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39722194005187279664500555 59583291007780919496750833)
                  ·
                    refine ⟨44687468255835689622563125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59583291007780919496750833 44687468255835689622563125)
                    ·
                      refine ⟨4189450148984595902115293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44687468255835689622563125 4189450148984595902115293)
                      ·
                        rfl

theorem cell23_8158925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_8158925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158925 prefixEnd_8158925 := by exact prefixLift 8158925
  have htrace : WordTrace (prefixWord ++ tailWord_8158925) baseStart_8158925 baseEnd_8158925 := by
    simpa [prefixWord, tailWord_8158925, baseEnd_8158925] using wordTrace_append hprefix tailTrace_8158925
  have hstable : (prefixWord ++ tailWord_8158925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158925).length < 2 ^ (prefixWord ++ tailWord_8158925).sum := by decide
  have hdescent : baseEnd_8158925 < baseStart_8158925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158958 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_8158958 : Nat := 118140960795 + 8158958 * 2 ^ 59
def prefixEnd_8158958 : Nat := 4983230072969 + 3 ^ 40 * 8158958 * 2
def baseEnd_8158958 : Nat := 465496343760688252555849

theorem tailTrace_8158958 : CollatzResearch.WordTrace tailWord_8158958 prefixEnd_8158958 465496343760688252555849 := by
  unfold tailWord_8158958
  simp only [CollatzResearch.WordTrace]
  refine ⟨37197705696937009991769691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198387763716997386622771685 37197705696937009991769691)
  ·
    refine ⟨55796558545405514987654537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37197705696937009991769691 55796558545405514987654537)
    ·
      refine ⟨41847418909054136240740903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55796558545405514987654537 41847418909054136240740903)
      ·
        refine ⟨62771128363581204361111355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41847418909054136240740903 62771128363581204361111355)
        ·
          refine ⟨94156692545371806541667033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62771128363581204361111355 94156692545371806541667033)
          ·
            refine ⟨70617519409028854906250275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94156692545371806541667033 70617519409028854906250275)
            ·
              refine ⟨105926279113543282359375413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70617519409028854906250275 105926279113543282359375413)
              ·
                refine ⟨9930588666894682721191445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105926279113543282359375413 9930588666894682721191445)
                ·
                  refine ⟨465496343760688252555849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9930588666894682721191445 465496343760688252555849)
                  ·
                    rfl

theorem cell23_8158958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_8158958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158958 prefixEnd_8158958 := by exact prefixLift 8158958
  have htrace : WordTrace (prefixWord ++ tailWord_8158958) baseStart_8158958 baseEnd_8158958 := by
    simpa [prefixWord, tailWord_8158958, baseEnd_8158958] using wordTrace_append hprefix tailTrace_8158958
  have hstable : (prefixWord ++ tailWord_8158958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158958).length < 2 ^ (prefixWord ++ tailWord_8158958).sum := by decide
  have hdescent : baseEnd_8158958 < baseStart_8158958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158981 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_8158981 : Nat := 118140960795 + 8158981 * 2 ^ 59
def prefixEnd_8158981 : Nat := 4983230072969 + 3 ^ 40 * 8158981 * 2
def baseEnd_8158981 : Nat := 4189478903901247683015035

theorem tailTrace_8158981 : CollatzResearch.WordTrace tailWord_8158981 prefixEnd_8158981 4189478903901247683015035 := by
  unfold tailWord_8158981
  simp only [CollatzResearch.WordTrace]
  refine ⟨297582484454412754862244797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198388322969608503241496531 297582484454412754862244797)
  ·
    refine ⟨111593431670404783073341799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297582484454412754862244797 111593431670404783073341799)
    ·
      refine ⟨167390147505607174610012699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111593431670404783073341799 167390147505607174610012699)
      ·
        refine ⟨251085221258410761915019049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167390147505607174610012699 251085221258410761915019049)
        ·
          refine ⟨188313915943808071436264287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251085221258410761915019049 188313915943808071436264287)
          ·
            refine ⟨282470873915712107154396431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188313915943808071436264287 282470873915712107154396431)
            ·
              refine ⟨423706310873568160731594647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282470873915712107154396431 423706310873568160731594647)
              ·
                refine ⟨635559466310352241097391971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423706310873568160731594647 635559466310352241097391971)
                ·
                  refine ⟨953339199465528361646087957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635559466310352241097391971 953339199465528361646087957)
                  ·
                    refine ⟨44687774974946641952160373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 953339199465528361646087957 44687774974946641952160373)
                    ·
                      refine ⟨4189478903901247683015035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44687774974946641952160373 4189478903901247683015035)
                      ·
                        rfl

theorem cell23_8158981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_8158981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158981 prefixEnd_8158981 := by exact prefixLift 8158981
  have htrace : WordTrace (prefixWord ++ tailWord_8158981) baseStart_8158981 baseEnd_8158981 := by
    simpa [prefixWord, tailWord_8158981, baseEnd_8158981] using wordTrace_append hprefix tailTrace_8158981
  have hstable : (prefixWord ++ tailWord_8158981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158981).length < 2 ^ (prefixWord ++ tailWord_8158981).sum := by decide
  have hdescent : baseEnd_8158981 < baseStart_8158981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8158996 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_8158996 : Nat := 118140960795 + 8158996 * 2 ^ 59
def prefixEnd_8158996 : Nat := 4983230072969 + 3 ^ 40 * 8158996 * 2
def baseEnd_8158996 : Nat := 1396495535370355041442489

theorem tailTrace_8158996 : CollatzResearch.WordTrace tailWord_8158996 prefixEnd_8158996 1396495535370355041442489 := by
  unfold tailWord_8158996
  simp only [CollatzResearch.WordTrace]
  refine ⟨148791515774679206212020421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198388687699572274949360561 148791515774679206212020421)
  ·
    refine ⟨27898409207752351164753829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148791515774679206212020421 27898409207752351164753829)
    ·
      refine ⟨5230951726453565843391343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27898409207752351164753829 5230951726453565843391343)
      ·
        refine ⟨7846427589680348765087015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230951726453565843391343 7846427589680348765087015)
        ·
          refine ⟨11769641384520523147630523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846427589680348765087015 11769641384520523147630523)
          ·
            refine ⟨17654462076780784721445785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769641384520523147630523 17654462076780784721445785)
            ·
              refine ⟨13240846557585588541084339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17654462076780784721445785 13240846557585588541084339)
              ·
                refine ⟨19861269836378382811626509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240846557585588541084339 19861269836378382811626509)
                ·
                  refine ⟨7447976188641893554359941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19861269836378382811626509 7447976188641893554359941)
                  ·
                    refine ⟨1396495535370355041442489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7447976188641893554359941 1396495535370355041442489)
                    ·
                      rfl

theorem cell23_8158996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_8158996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8158996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8158996 prefixEnd_8158996 := by exact prefixLift 8158996
  have htrace : WordTrace (prefixWord ++ tailWord_8158996) baseStart_8158996 baseEnd_8158996 := by
    simpa [prefixWord, tailWord_8158996, baseEnd_8158996] using wordTrace_append hprefix tailTrace_8158996
  have hstable : (prefixWord ++ tailWord_8158996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8158996).length < 2 ^ (prefixWord ++ tailWord_8158996).sum := by decide
  have hdescent : baseEnd_8158996 < baseStart_8158996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8158996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159002 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_8159002 : Nat := 118140960795 + 8159002 * 2 ^ 59
def prefixEnd_8159002 : Nat := 4983230072969 + 3 ^ 40 * 8159002 * 2
def baseEnd_8159002 : Nat := 4189489686994992100852439

theorem tailTrace_8159002 : CollatzResearch.WordTrace tailWord_8159002 prefixEnd_8159002 4189489686994992100852439 := by
  unfold tailWord_8159002
  simp only [CollatzResearch.WordTrace]
  refine ⟨74395812596834168862189815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198388833591557783632506173 74395812596834168862189815)
  ·
    refine ⟨111593718895251253293284723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74395812596834168862189815 111593718895251253293284723)
    ·
      refine ⟨167390578342876879939927085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111593718895251253293284723 167390578342876879939927085)
      ·
        refine ⟨62771466878578829977472657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167390578342876879939927085 62771466878578829977472657)
        ·
          refine ⟨47078600158934122483104493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62771466878578829977472657 47078600158934122483104493)
          ·
            refine ⟨17654475059600295931164185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47078600158934122483104493 17654475059600295931164185)
            ·
              refine ⟨13240856294700221948373139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17654475059600295931164185 13240856294700221948373139)
              ·
                refine ⟨19861284442050332922559709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240856294700221948373139 19861284442050332922559709)
                ·
                  refine ⟨7447981665768874845959891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19861284442050332922559709 7447981665768874845959891)
                  ·
                    refine ⟨11171972498653312268939837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7447981665768874845959891 11171972498653312268939837)
                    ·
                      refine ⟨4189489686994992100852439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11171972498653312268939837 4189489686994992100852439)
                      ·
                        rfl

theorem cell23_8159002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_8159002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159002 prefixEnd_8159002 := by exact prefixLift 8159002
  have htrace : WordTrace (prefixWord ++ tailWord_8159002) baseStart_8159002 baseEnd_8159002 := by
    simpa [prefixWord, tailWord_8159002, baseEnd_8159002] using wordTrace_append hprefix tailTrace_8159002
  have hstable : (prefixWord ++ tailWord_8159002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159002).length < 2 ^ (prefixWord ++ tailWord_8159002).sum := by decide
  have hdescent : baseEnd_8159002 < baseStart_8159002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159025 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_8159025 : Nat := 118140960795 + 8159025 * 2 ^ 59
def prefixEnd_8159025 : Nat := 4983230072969 + 3 ^ 40 * 8159025 * 2
def baseEnd_8159025 : Nat := 4189501497050045510864833

theorem tailTrace_8159025 : CollatzResearch.WordTrace tailWord_8159025 prefixEnd_8159025 4189501497050045510864833 := by
  unfold tailWord_8159025
  simp only [CollatzResearch.WordTrace]
  refine ⟨297584089266253350376846529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198389392844168900251231019 297584089266253350376846529)
  ·
    refine ⟨223188066949690012782634897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297584089266253350376846529 223188066949690012782634897)
    ·
      refine ⟨167391050212267509586976173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223188066949690012782634897 167391050212267509586976173)
      ·
        refine ⟨62771643829600316095116065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167391050212267509586976173 62771643829600316095116065)
        ·
          refine ⟨47078732872200237071337049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62771643829600316095116065 47078732872200237071337049)
          ·
            refine ⟨35309049654150177803502787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47078732872200237071337049 35309049654150177803502787)
            ·
              refine ⟨52963574481225266705254181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35309049654150177803502787 52963574481225266705254181)
              ·
                refine ⟨9930670215229737507235159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52963574481225266705254181 9930670215229737507235159)
                ·
                  refine ⟨14896005322844606260852739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9930670215229737507235159 14896005322844606260852739)
                  ·
                    refine ⟨22344007984266909391279109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14896005322844606260852739 22344007984266909391279109)
                    ·
                      refine ⟨4189501497050045510864833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22344007984266909391279109 4189501497050045510864833)
                      ·
                        rfl

theorem cell23_8159025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_8159025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159025 prefixEnd_8159025 := by exact prefixLift 8159025
  have htrace : WordTrace (prefixWord ++ tailWord_8159025) baseStart_8159025 baseEnd_8159025 := by
    simpa [prefixWord, tailWord_8159025, baseEnd_8159025] using wordTrace_append hprefix tailTrace_8159025
  have hstable : (prefixWord ++ tailWord_8159025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159025).length < 2 ^ (prefixWord ++ tailWord_8159025).sum := by decide
  have hdescent : baseEnd_8159025 < baseStart_8159025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159045 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_8159045 : Nat := 118140960795 + 8159045 * 2 ^ 59
def prefixEnd_8159045 : Nat := 4983230072969 + 3 ^ 40 * 8159045 * 2
def baseEnd_8159045 : Nat := 4189511766663135432614741

theorem tailTrace_8159045 : CollatzResearch.WordTrace tailWord_8159045 prefixEnd_8159045 4189511766663135432614741 := by
  unfold tailWord_8159045
  simp only [CollatzResearch.WordTrace]
  refine ⟨297584818726180893792574589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198389879150787262528383059 297584818726180893792574589)
  ·
    refine ⟨111594307022317835172215471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297584818726180893792574589 111594307022317835172215471)
    ·
      refine ⟨167391460533476752758323207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111594307022317835172215471 167391460533476752758323207)
      ·
        refine ⟨251087190800215129137484811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167391460533476752758323207 251087190800215129137484811)
        ·
          refine ⟨376630786200322693706227217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251087190800215129137484811 376630786200322693706227217)
          ·
            refine ⟨282473089650242020279670413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376630786200322693706227217 282473089650242020279670413)
            ·
              refine ⟨105927408618840757604876405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282473089650242020279670413 105927408618840757604876405)
              ·
                refine ⟨9930694558016321025457163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105927408618840757604876405 9930694558016321025457163)
                ·
                  refine ⟨14896041837024481538185745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9930694558016321025457163 14896041837024481538185745)
                  ·
                    refine ⟨11172031377768361153639309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14896041837024481538185745 11172031377768361153639309)
                    ·
                      refine ⟨4189511766663135432614741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11172031377768361153639309 4189511766663135432614741)
                      ·
                        rfl

theorem cell23_8159045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_8159045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159045 prefixEnd_8159045 := by exact prefixLift 8159045
  have htrace : WordTrace (prefixWord ++ tailWord_8159045) baseStart_8159045 baseEnd_8159045 := by
    simpa [prefixWord, tailWord_8159045, baseEnd_8159045] using wordTrace_append hprefix tailTrace_8159045
  have hstable : (prefixWord ++ tailWord_8159045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159045).length < 2 ^ (prefixWord ++ tailWord_8159045).sum := by decide
  have hdescent : baseEnd_8159045 < baseStart_8159045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159046 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_8159046 : Nat := 118140960795 + 8159046 * 2 ^ 59
def prefixEnd_8159046 : Nat := 4983230072969 + 3 ^ 40 * 8159046 * 2
def baseEnd_8159046 : Nat := 4189512280143789928702237

theorem tailTrace_8159046 : CollatzResearch.WordTrace tailWord_8159046 prefixEnd_8159046 4189512280143789928702237 := by
  unfold tailWord_8159046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9299526724974289717605031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198389903466118180642240661 9299526724974289717605031)
  ·
    refine ⟨13949290087461434576407547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9299526724974289717605031 13949290087461434576407547)
    ·
      refine ⟨20923935131192151864611321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13949290087461434576407547 20923935131192151864611321)
      ·
        refine ⟨15692951348394113898458491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20923935131192151864611321 15692951348394113898458491)
        ·
          refine ⟨23539427022591170847687737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15692951348394113898458491 23539427022591170847687737)
          ·
            refine ⟨17654570266943378135765803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23539427022591170847687737 17654570266943378135765803)
            ·
              refine ⟨26481855400415067203648705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17654570266943378135765803 26481855400415067203648705)
              ·
                refine ⟨19861391550311300402736529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26481855400415067203648705 19861391550311300402736529)
                ·
                  refine ⟨14896043662733475302052397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19861391550311300402736529 14896043662733475302052397)
                  ·
                    refine ⟨5586016373525053238269649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14896043662733475302052397 5586016373525053238269649)
                    ·
                      refine ⟨4189512280143789928702237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586016373525053238269649 4189512280143789928702237)
                      ·
                        rfl

theorem cell23_8159046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_8159046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159046 prefixEnd_8159046 := by exact prefixLift 8159046
  have htrace : WordTrace (prefixWord ++ tailWord_8159046) baseStart_8159046 baseEnd_8159046 := by
    simpa [prefixWord, tailWord_8159046, baseEnd_8159046] using wordTrace_append hprefix tailTrace_8159046
  have hstable : (prefixWord ++ tailWord_8159046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159046).length < 2 ^ (prefixWord ++ tailWord_8159046).sum := by decide
  have hdescent : baseEnd_8159046 < baseStart_8159046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159048 : List Nat := [2, 1, 3, 1, 1, 6, 9]
def baseStart_8159048 : Nat := 118140960795 + 8159048 * 2 ^ 59
def prefixEnd_8159048 : Nat := 4983230072969 + 3 ^ 40 * 8159048 * 2
def baseEnd_8159048 : Nat := 51722386507470357047867

theorem tailTrace_8159048 : CollatzResearch.WordTrace tailWord_8159048 prefixEnd_8159048 51722386507470357047867 := by
  unfold tailWord_8159048
  simp only [CollatzResearch.WordTrace]
  refine ⟨148792464072585012652466899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198389952096780016869955865 148792464072585012652466899)
  ·
    refine ⟨223188696108877518978700349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148792464072585012652466899 223188696108877518978700349)
    ·
      refine ⟨83695761040829069617012631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223188696108877518978700349 83695761040829069617012631)
      ·
        refine ⟨125543641561243604425518947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83695761040829069617012631 125543641561243604425518947)
        ·
          refine ⟨188315462341865406638278421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125543641561243604425518947 188315462341865406638278421)
          ·
            refine ⟨8827287297274940936169301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188315462341865406638278421 8827287297274940936169301)
            ·
              refine ⟨51722386507470357047867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8827287297274940936169301 51722386507470357047867)
              ·
                rfl

theorem cell23_8159048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 9].length) (baseStart_8159048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159048 prefixEnd_8159048 := by exact prefixLift 8159048
  have htrace : WordTrace (prefixWord ++ tailWord_8159048) baseStart_8159048 baseEnd_8159048 := by
    simpa [prefixWord, tailWord_8159048, baseEnd_8159048] using wordTrace_append hprefix tailTrace_8159048
  have hstable : (prefixWord ++ tailWord_8159048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159048).length < 2 ^ (prefixWord ++ tailWord_8159048).sum := by decide
  have hdescent : baseEnd_8159048 < baseStart_8159048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159053 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_8159053 : Nat := 118140960795 + 8159053 * 2 ^ 59
def prefixEnd_8159053 : Nat := 4983230072969 + 3 ^ 40 * 8159053 * 2
def baseEnd_8159053 : Nat := 4189515874508371401314705

theorem tailTrace_8159053 : CollatzResearch.WordTrace tailWord_8159053 prefixEnd_8159053 4189515874508371401314705 := by
  unfold tailWord_8159053
  simp only [CollatzResearch.WordTrace]
  refine ⟨297585110510151911158865813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198390073673434607439243875 297585110510151911158865813)
  ·
    refine ⟨13949302055163370835571835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297585110510151911158865813 13949302055163370835571835)
    ·
      refine ⟨20923953082745056253357753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13949302055163370835571835 20923953082745056253357753)
      ·
        refine ⟨15692964812058792190018315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20923953082745056253357753 15692964812058792190018315)
        ·
          refine ⟨23539447218088188285027473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15692964812058792190018315 23539447218088188285027473)
          ·
            refine ⟨17654585413566141213770605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23539447218088188285027473 17654585413566141213770605)
            ·
              refine ⟨6620469530087302955163977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17654585413566141213770605 6620469530087302955163977)
              ·
                refine ⟨4965352147565477216372983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6620469530087302955163977 4965352147565477216372983)
                ·
                  refine ⟨7448028221348215824559475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965352147565477216372983 7448028221348215824559475)
                  ·
                    refine ⟨11172042332022323736839213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7448028221348215824559475 11172042332022323736839213)
                    ·
                      refine ⟨4189515874508371401314705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11172042332022323736839213 4189515874508371401314705)
                      ·
                        rfl

theorem cell23_8159053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_8159053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159053 prefixEnd_8159053 := by exact prefixLift 8159053
  have htrace : WordTrace (prefixWord ++ tailWord_8159053) baseStart_8159053 baseEnd_8159053 := by
    simpa [prefixWord, tailWord_8159053, baseEnd_8159053] using wordTrace_append hprefix tailTrace_8159053
  have hstable : (prefixWord ++ tailWord_8159053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159053).length < 2 ^ (prefixWord ++ tailWord_8159053).sum := by decide
  have hdescent : baseEnd_8159053 < baseStart_8159053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159115 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 5, 4, 2]
def baseStart_8159115 : Nat := 118140960795 + 8159115 * 2 ^ 59
def prefixEnd_8159115 : Nat := 4983230072969 + 3 ^ 40 * 8159115 * 2
def baseEnd_8159115 : Nat := 4189547710308950158739419

theorem tailTrace_8159115 : CollatzResearch.WordTrace tailWord_8159115 prefixEnd_8159115 4189547710308950158739419 := by
  unfold tailWord_8159115
  simp only [CollatzResearch.WordTrace]
  refine ⟨297587371835927295747622799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198391581223951530498415199 297587371835927295747622799)
  ·
    refine ⟨446381057753890943621434199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297587371835927295747622799 446381057753890943621434199)
    ·
      refine ⟨669571586630836415432151299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446381057753890943621434199 669571586630836415432151299)
      ·
        refine ⟨1004357379946254623148226949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669571586630836415432151299 1004357379946254623148226949)
        ·
          refine ⟨188317008739922741840292553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1004357379946254623148226949 188317008739922741840292553)
          ·
            refine ⟨141237756554942056380219415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188317008739922741840292553 141237756554942056380219415)
            ·
              refine ⟨211856634832413084570329123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141237756554942056380219415 211856634832413084570329123)
              ·
                refine ⟨317784952248619626855493685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211856634832413084570329123 317784952248619626855493685)
                ·
                  refine ⟨29792339273308090017702533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317784952248619626855493685 29792339273308090017702533)
                  ·
                    refine ⟨5586063613745266878319225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29792339273308090017702533 5586063613745266878319225)
                    ·
                      refine ⟨4189547710308950158739419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586063613745266878319225 4189547710308950158739419)
                      ·
                        rfl

theorem cell23_8159115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4, 2].length) (baseStart_8159115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159115 prefixEnd_8159115 := by exact prefixLift 8159115
  have htrace : WordTrace (prefixWord ++ tailWord_8159115) baseStart_8159115 baseEnd_8159115 := by
    simpa [prefixWord, tailWord_8159115, baseEnd_8159115] using wordTrace_append hprefix tailTrace_8159115
  have hstable : (prefixWord ++ tailWord_8159115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159115).length < 2 ^ (prefixWord ++ tailWord_8159115).sum := by decide
  have hdescent : baseEnd_8159115 < baseStart_8159115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159166 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_8159166 : Nat := 118140960795 + 8159166 * 2 ^ 59
def prefixEnd_8159166 : Nat := 4983230072969 + 3 ^ 40 * 8159166 * 2
def baseEnd_8159166 : Nat := 4189573897822329459201685

theorem tailTrace_8159166 : CollatzResearch.WordTrace tailWord_8159166 prefixEnd_8159166 4189573897822329459201685 := by
  unfold tailWord_8159166
  simp only [CollatzResearch.WordTrace]
  refine ⟨37198653994842816432216169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198392821305828354305152901 37198653994842816432216169)
  ·
    refine ⟨27898990496132112324162127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37198653994842816432216169 27898990496132112324162127)
    ·
      refine ⟨41848485744198168486243191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27898990496132112324162127 41848485744198168486243191)
      ·
        refine ⟨62772728616297252729364787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41848485744198168486243191 62772728616297252729364787)
        ·
          refine ⟨94159092924445879094047181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62772728616297252729364787 94159092924445879094047181)
          ·
            refine ⟨35309659846667204660267693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94159092924445879094047181 35309659846667204660267693)
            ·
              refine ⟨13241122442500201747600385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35309659846667204660267693 13241122442500201747600385)
              ·
                refine ⟨9930841831875151310700289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13241122442500201747600385 9930841831875151310700289)
                ·
                  refine ⟨7448131373906363483025217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9930841831875151310700289 7448131373906363483025217)
                  ·
                    refine ⟨5586098530429772612268913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448131373906363483025217 5586098530429772612268913)
                    ·
                      refine ⟨4189573897822329459201685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586098530429772612268913 4189573897822329459201685)
                      ·
                        rfl

theorem cell23_8159166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_8159166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159166 prefixEnd_8159166 := by exact prefixLift 8159166
  have htrace : WordTrace (prefixWord ++ tailWord_8159166) baseStart_8159166 baseEnd_8159166 := by
    simpa [prefixWord, tailWord_8159166, baseEnd_8159166] using wordTrace_append hprefix tailTrace_8159166
  have hstable : (prefixWord ++ tailWord_8159166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159166).length < 2 ^ (prefixWord ++ tailWord_8159166).sum := by decide
  have hdescent : baseEnd_8159166 < baseStart_8159166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159309 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_8159309 : Nat := 118140960795 + 8159309 * 2 ^ 59
def prefixEnd_8159309 : Nat := 4983230072969 + 3 ^ 40 * 8159309 * 2
def baseEnd_8159309 : Nat := 1396549108518640799904509

theorem tailTrace_8159309 : CollatzResearch.WordTrace tailWord_8159309 prefixEnd_8159309 1396549108518640799904509 := by
  unfold tailWord_8159309
  simp only [CollatzResearch.WordTrace]
  refine ⟨297594447597224466880184981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198396298398149644586789987 297594447597224466880184981)
  ·
    refine ⟨13949739731119896885008671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297594447597224466880184981 13949739731119896885008671)
    ·
      refine ⟨20924609596679845327513007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13949739731119896885008671 20924609596679845327513007)
      ·
        refine ⟨31386914395019767991269511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20924609596679845327513007 31386914395019767991269511)
        ·
          refine ⟨47080371592529651986904267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31386914395019767991269511 47080371592529651986904267)
          ·
            refine ⟨70620557388794477980356401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47080371592529651986904267 70620557388794477980356401)
            ·
              refine ⟨52965418041595858485267301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70620557388794477980356401 52965418041595858485267301)
              ·
                refine ⟨9931015882799223465987619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52965418041595858485267301 9931015882799223465987619)
                ·
                  refine ⟨14896523824198835198981429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931015882799223465987619 14896523824198835198981429)
                  ·
                    refine ⟨1396549108518640799904509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14896523824198835198981429 1396549108518640799904509)
                    ·
                      rfl

theorem cell23_8159309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_8159309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159309 prefixEnd_8159309 := by exact prefixLift 8159309
  have htrace : WordTrace (prefixWord ++ tailWord_8159309) baseStart_8159309 baseEnd_8159309 := by
    simpa [prefixWord, tailWord_8159309, baseEnd_8159309] using wordTrace_append hprefix tailTrace_8159309
  have hstable : (prefixWord ++ tailWord_8159309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159309).length < 2 ^ (prefixWord ++ tailWord_8159309).sum := by decide
  have hdescent : baseEnd_8159309 < baseStart_8159309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159322 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_8159322 : Nat := 118140960795 + 8159322 * 2 ^ 59
def prefixEnd_8159322 : Nat := 4983230072969 + 3 ^ 40 * 8159322 * 2
def baseEnd_8159322 : Nat := 1396551333601476949616989

theorem tailTrace_8159322 : CollatzResearch.WordTrace tailWord_8159322 prefixEnd_8159322 1396551333601476949616989 := by
  unfold tailWord_8159322
  simp only [CollatzResearch.WordTrace]
  refine ⟨74398730436544342525102055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198396614497451580066938813 74398730436544342525102055)
  ·
    refine ⟨111598095654816513787653083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74398730436544342525102055 111598095654816513787653083)
    ·
      refine ⟨167397143482224770681479625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111598095654816513787653083 167397143482224770681479625)
      ·
        refine ⟨125547857611668578011109719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167397143482224770681479625 125547857611668578011109719)
        ·
          refine ⟨188321786417502867016664579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125547857611668578011109719 188321786417502867016664579)
          ·
            refine ⟨282482679626254300524996869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188321786417502867016664579 282482679626254300524996869)
            ·
              refine ⟨52965502429922681348436913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282482679626254300524996869 52965502429922681348436913)
              ·
                refine ⟨39724126822442011011327685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52965502429922681348436913 39724126822442011011327685)
                ·
                  refine ⟨7448273779207877064623941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39724126822442011011327685 7448273779207877064623941)
                  ·
                    refine ⟨1396551333601476949616989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448273779207877064623941 1396551333601476949616989)
                    ·
                      rfl

theorem cell23_8159322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_8159322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159322 prefixEnd_8159322 := by exact prefixLift 8159322
  have htrace : WordTrace (prefixWord ++ tailWord_8159322) baseStart_8159322 baseEnd_8159322 := by
    simpa [prefixWord, tailWord_8159322, baseEnd_8159322] using wordTrace_append hprefix tailTrace_8159322
  have hstable : (prefixWord ++ tailWord_8159322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159322).length < 2 ^ (prefixWord ++ tailWord_8159322).sum := by decide
  have hdescent : baseEnd_8159322 < baseStart_8159322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159329 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_8159329 : Nat := 118140960795 + 8159329 * 2 ^ 59
def prefixEnd_8159329 : Nat := 4983230072969 + 3 ^ 40 * 8159329 * 2
def baseEnd_8159329 : Nat := 4189657595169012321463435

theorem tailTrace_8159329 : CollatzResearch.WordTrace tailWord_8159329 prefixEnd_8159329 4189657595169012321463435 := by
  unfold tailWord_8159329
  simp only [CollatzResearch.WordTrace]
  refine ⟨297595177057152010295913041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198396784704768006863942027 297595177057152010295913041)
  ·
    refine ⟨223196382792864007721934781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297595177057152010295913041 223196382792864007721934781)
    ·
      refine ⟨83698643547324002895725543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223196382792864007721934781 83698643547324002895725543)
      ·
        refine ⟨125547965320986004343588315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83698643547324002895725543 125547965320986004343588315)
        ·
          refine ⟨188321947981479006515382473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125547965320986004343588315 188321947981479006515382473)
          ·
            refine ⟨141241460986109254886536855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188321947981479006515382473 141241460986109254886536855)
            ·
              refine ⟨211862191479163882329805283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141241460986109254886536855 211862191479163882329805283)
              ·
                refine ⟨317793287218745823494707925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211862191479163882329805283 317793287218745823494707925)
                ·
                  refine ⟨7448280169189355238157217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 317793287218745823494707925 7448280169189355238157217)
                  ·
                    refine ⟨5586210126892016428617913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448280169189355238157217 5586210126892016428617913)
                    ·
                      refine ⟨4189657595169012321463435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586210126892016428617913 4189657595169012321463435)
                      ·
                        rfl

theorem cell23_8159329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_8159329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159329 prefixEnd_8159329 := by exact prefixLift 8159329
  have htrace : WordTrace (prefixWord ++ tailWord_8159329) baseStart_8159329 baseEnd_8159329 := by
    simpa [prefixWord, tailWord_8159329, baseEnd_8159329] using wordTrace_append hprefix tailTrace_8159329
  have hstable : (prefixWord ++ tailWord_8159329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159329).length < 2 ^ (prefixWord ++ tailWord_8159329).sum := by decide
  have hdescent : baseEnd_8159329 < baseStart_8159329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159335 : List Nat := [1, 1, 5, 1, 1, 2, 12]
def baseStart_8159335 : Nat := 118140960795 + 8159335 * 2 ^ 59
def prefixEnd_8159335 : Nat := 4983230072969 + 3 ^ 40 * 8159335 * 2
def baseEnd_8159335 : Nat := 51724205877196781456647

theorem tailTrace_8159335 : CollatzResearch.WordTrace tailWord_8159335 prefixEnd_8159335 51724205877196781456647 := by
  unfold tailWord_8159335
  simp only [CollatzResearch.WordTrace]
  refine ⟨297595395895130273320631459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198396930596753515547087639 297595395895130273320631459)
  ·
    refine ⟨446393093842695409980947189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297595395895130273320631459 446393093842695409980947189)
    ·
      refine ⟨41849352547752694685713799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 446393093842695409980947189 41849352547752694685713799)
      ·
        refine ⟨62774028821629042028570699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41849352547752694685713799 62774028821629042028570699)
        ·
          refine ⟨94161043232443563042856049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62774028821629042028570699 94161043232443563042856049)
          ·
            refine ⟨70620782424332672282142037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94161043232443563042856049 70620782424332672282142037)
            ·
              refine ⟨51724205877196781456647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 70620782424332672282142037 51724205877196781456647)
              ·
                rfl

theorem cell23_8159335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 12].length) (baseStart_8159335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159335 prefixEnd_8159335 := by exact prefixLift 8159335
  have htrace : WordTrace (prefixWord ++ tailWord_8159335) baseStart_8159335 baseEnd_8159335 := by
    simpa [prefixWord, tailWord_8159335, baseEnd_8159335] using wordTrace_append hprefix tailTrace_8159335
  have hstable : (prefixWord ++ tailWord_8159335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159335).length < 2 ^ (prefixWord ++ tailWord_8159335).sum := by decide
  have hdescent : baseEnd_8159335 < baseStart_8159335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159342 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_8159342 : Nat := 118140960795 + 8159342 * 2 ^ 59
def prefixEnd_8159342 : Nat := 4983230072969 + 3 ^ 40 * 8159342 * 2
def baseEnd_8159342 : Nat := 4189664270417520770600875

theorem tailTrace_8159342 : CollatzResearch.WordTrace tailWord_8159342 prefixEnd_8159342 4189664270417520770600875 := by
  unfold tailWord_8159342
  simp only [CollatzResearch.WordTrace]
  refine ⟨37199456400763114189517035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198397100804069942344090853 37199456400763114189517035)
  ·
    refine ⟨55799184601144671284275553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37199456400763114189517035 55799184601144671284275553)
    ·
      refine ⟨41849388450858503463206665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55799184601144671284275553 41849388450858503463206665)
      ·
        refine ⟨31387041338143877597404999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41849388450858503463206665 31387041338143877597404999)
        ·
          refine ⟨47080562007215816396107499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31387041338143877597404999 47080562007215816396107499)
          ·
            refine ⟨70620843010823724594161249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47080562007215816396107499 70620843010823724594161249)
            ·
              refine ⟨52965632258117793445620937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70620843010823724594161249 52965632258117793445620937)
              ·
                refine ⟨39724224193588345084215703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52965632258117793445620937 39724224193588345084215703)
                ·
                  refine ⟨59586336290382517626323555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39724224193588345084215703 59586336290382517626323555)
                  ·
                    refine ⟨89379504435573776439485333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59586336290382517626323555 89379504435573776439485333)
                    ·
                      refine ⟨4189664270417520770600875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89379504435573776439485333 4189664270417520770600875)
                      ·
                        rfl

theorem cell23_8159342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_8159342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159342 prefixEnd_8159342 := by exact prefixLift 8159342
  have htrace : WordTrace (prefixWord ++ tailWord_8159342) baseStart_8159342 baseEnd_8159342 := by
    simpa [prefixWord, tailWord_8159342, baseEnd_8159342] using wordTrace_append hprefix tailTrace_8159342
  have hstable : (prefixWord ++ tailWord_8159342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159342).length < 2 ^ (prefixWord ++ tailWord_8159342).sum := by decide
  have hdescent : baseEnd_8159342 < baseStart_8159342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159346 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_8159346 : Nat := 118140960795 + 8159346 * 2 ^ 59
def prefixEnd_8159346 : Nat := 4983230072969 + 3 ^ 40 * 8159346 * 2
def baseEnd_8159346 : Nat := 4189666324340138754950857

theorem tailTrace_8159346 : CollatzResearch.WordTrace tailWord_8159346 prefixEnd_8159346 4189666324340138754950857 := by
  unfold tailWord_8159346
  simp only [CollatzResearch.WordTrace]
  refine ⟨74398949274522605549820473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198397198065393614799521261 74398949274522605549820473)
  ·
    refine ⟨55799211955891954162365355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74398949274522605549820473 55799211955891954162365355)
    ·
      refine ⟨83698817933837931243548033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55799211955891954162365355 83698817933837931243548033)
      ·
        refine ⟨62774113450378448432661025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83698817933837931243548033 62774113450378448432661025)
        ·
          refine ⟨47080585087783836324495769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62774113450378448432661025 47080585087783836324495769)
          ·
            refine ⟨35310438815837877243371827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47080585087783836324495769 35310438815837877243371827)
            ·
              refine ⟨52965658223756815865057741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35310438815837877243371827 52965658223756815865057741)
              ·
                refine ⟨19862121833908805949396653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52965658223756815865057741 19862121833908805949396653)
                ·
                  refine ⟨7448295687715802231023745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19862121833908805949396653 7448295687715802231023745)
                  ·
                    refine ⟨5586221765786851673267809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448295687715802231023745 5586221765786851673267809)
                    ·
                      refine ⟨4189666324340138754950857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586221765786851673267809 4189666324340138754950857)
                      ·
                        rfl

theorem cell23_8159346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_8159346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159346 prefixEnd_8159346 := by exact prefixLift 8159346
  have htrace : WordTrace (prefixWord ++ tailWord_8159346) baseStart_8159346 baseEnd_8159346 := by
    simpa [prefixWord, tailWord_8159346, baseEnd_8159346] using wordTrace_append hprefix tailTrace_8159346
  have hstable : (prefixWord ++ tailWord_8159346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159346).length < 2 ^ (prefixWord ++ tailWord_8159346).sum := by decide
  have hdescent : baseEnd_8159346 < baseStart_8159346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159356 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_8159356 : Nat := 118140960795 + 8159356 * 2 ^ 59
def prefixEnd_8159356 : Nat := 4983230072969 + 3 ^ 40 * 8159356 * 2
def baseEnd_8159356 : Nat := 1396557153048894571941937

theorem tailTrace_8159356 : CollatzResearch.WordTrace tailWord_8159356 prefixEnd_8159356 1396557153048894571941937 := by
  unfold tailWord_8159356
  simp only [CollatzResearch.WordTrace]
  refine ⟨148798080914027096953572961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198397441218702795938097281 148798080914027096953572961)
  ·
    refine ⟨111598560685520322715179721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148798080914027096953572961 111598560685520322715179721)
    ·
      refine ⟨83698920514140242036384791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111598560685520322715179721 83698920514140242036384791)
      ·
        refine ⟨125548380771210363054577187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83698920514140242036384791 125548380771210363054577187)
        ·
          refine ⟨188322571156815544581865781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125548380771210363054577187 188322571156815544581865781)
          ·
            refine ⟨17655241045951457304549917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188322571156815544581865781 17655241045951457304549917)
            ·
              refine ⟨6620715392231796489206219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17655241045951457304549917 6620715392231796489206219)
              ·
                refine ⟨9931073088347694733809329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620715392231796489206219 9931073088347694733809329)
                ·
                  refine ⟨7448304816260771050356997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9931073088347694733809329 7448304816260771050356997)
                  ·
                    refine ⟨1396557153048894571941937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448304816260771050356997 1396557153048894571941937)
                    ·
                      rfl

theorem cell23_8159356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_8159356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159356 prefixEnd_8159356 := by exact prefixLift 8159356
  have htrace : WordTrace (prefixWord ++ tailWord_8159356) baseStart_8159356 baseEnd_8159356 := by
    simpa [prefixWord, tailWord_8159356, baseEnd_8159356] using wordTrace_append hprefix tailTrace_8159356
  have hstable : (prefixWord ++ tailWord_8159356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159356).length < 2 ^ (prefixWord ++ tailWord_8159356).sum := by decide
  have hdescent : baseEnd_8159356 < baseStart_8159356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159385 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_8159385 : Nat := 118140960795 + 8159385 * 2 ^ 59
def prefixEnd_8159385 : Nat := 4983230072969 + 3 ^ 40 * 8159385 * 2
def baseEnd_8159385 : Nat := 4189686350085664102363177

theorem tailTrace_8159385 : CollatzResearch.WordTrace tailWord_8159385 prefixEnd_8159385 4189686350085664102363177 := by
  unfold tailWord_8159385
  simp only [CollatzResearch.WordTrace]
  refine ⟨297597219544949131859951609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198398146363299421239967739 297597219544949131859951609)
  ·
    refine ⟨223197914658711848894963707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297597219544949131859951609 223197914658711848894963707)
    ·
      refine ⟨334796871988067773342445561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223197914658711848894963707 334796871988067773342445561)
      ·
        refine ⟨251097653991050830006834171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334796871988067773342445561 251097653991050830006834171)
        ·
          refine ⟨376646480986576245010251257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251097653991050830006834171 376646480986576245010251257)
          ·
            refine ⟨282484860739932183757688443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376646480986576245010251257 282484860739932183757688443)
            ·
              refine ⟨423727291109898275636532665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282484860739932183757688443 423727291109898275636532665)
              ·
                refine ⟨317795468332423706727399499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423727291109898275636532665 317795468332423706727399499)
                ·
                  refine ⟨476693202498635560091099249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317795468332423706727399499 476693202498635560091099249)
                  ·
                    refine ⟨357519901873976670068324437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476693202498635560091099249 357519901873976670068324437)
                    ·
                      refine ⟨4189686350085664102363177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357519901873976670068324437 4189686350085664102363177)
                      ·
                        rfl

theorem cell23_8159385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_8159385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159385 prefixEnd_8159385 := by exact prefixLift 8159385
  have htrace : WordTrace (prefixWord ++ tailWord_8159385) baseStart_8159385 baseEnd_8159385 := by
    simpa [prefixWord, tailWord_8159385, baseEnd_8159385] using wordTrace_append hprefix tailTrace_8159385
  have hstable : (prefixWord ++ tailWord_8159385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159385).length < 2 ^ (prefixWord ++ tailWord_8159385).sum := by decide
  have hdescent : baseEnd_8159385 < baseStart_8159385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159419 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 1, 4, 2]
def baseStart_8159419 : Nat := 118140960795 + 8159419 * 2 ^ 59
def prefixEnd_8159419 : Nat := 4983230072969 + 3 ^ 40 * 8159419 * 2
def baseEnd_8159419 : Nat := 4189703808427916969338021

theorem tailTrace_8159419 : CollatzResearch.WordTrace tailWord_8159419 prefixEnd_8159419 4189703808427916969338021 := by
  unfold tailWord_8159419
  simp only [CollatzResearch.WordTrace]
  refine ⟨297598459626825955666689311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198398973084550637111126207 297598459626825955666689311)
  ·
    refine ⟨446397689440238933500033967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297598459626825955666689311 446397689440238933500033967)
    ·
      refine ⟨669596534160358400250050951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446397689440238933500033967 669596534160358400250050951)
      ·
        refine ⟨1004394801240537600375076427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669596534160358400250050951 1004394801240537600375076427)
        ·
          refine ⟨1506592201860806400562614641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004394801240537600375076427 1506592201860806400562614641)
          ·
            refine ⟨1129944151395604800421960981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506592201860806400562614641 1129944151395604800421960981)
            ·
              refine ⟨52966132096668975019779421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1129944151395604800421960981 52966132096668975019779421)
              ·
                refine ⟨19862299536250865632417283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52966132096668975019779421 19862299536250865632417283)
                ·
                  refine ⟨29793449304376298448625925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19862299536250865632417283 29793449304376298448625925)
                  ·
                    refine ⟨5586271744570555959117361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29793449304376298448625925 5586271744570555959117361)
                    ·
                      refine ⟨4189703808427916969338021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586271744570555959117361 4189703808427916969338021)
                      ·
                        rfl

theorem cell23_8159419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4, 2].length) (baseStart_8159419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159419 prefixEnd_8159419 := by exact prefixLift 8159419
  have htrace : WordTrace (prefixWord ++ tailWord_8159419) baseStart_8159419 baseEnd_8159419 := by
    simpa [prefixWord, tailWord_8159419, baseEnd_8159419] using wordTrace_append hprefix tailTrace_8159419
  have hstable : (prefixWord ++ tailWord_8159419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159419).length < 2 ^ (prefixWord ++ tailWord_8159419).sum := by decide
  have hdescent : baseEnd_8159419 < baseStart_8159419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159432 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_8159432 : Nat := 118140960795 + 8159432 * 2 ^ 59
def prefixEnd_8159432 : Nat := 4983230072969 + 3 ^ 40 * 8159432 * 2
def baseEnd_8159432 : Nat := 4189710483676425418475461

theorem tailTrace_8159432 : CollatzResearch.WordTrace tailWord_8159432 prefixEnd_8159432 4189710483676425418475461 := by
  unfold tailWord_8159432
  simp only [CollatzResearch.WordTrace]
  refine ⟨148799466887889429443456275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198399289183852572591275033 148799466887889429443456275)
  ·
    refine ⟨223199200331834144165184413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148799466887889429443456275 223199200331834144165184413)
    ·
      refine ⟨83699700124437804061944155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223199200331834144165184413 83699700124437804061944155)
      ·
        refine ⟨125549550186656706092916233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83699700124437804061944155 125549550186656706092916233)
        ·
          refine ⟨94162162639992529569687175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125549550186656706092916233 94162162639992529569687175)
          ·
            refine ⟨141243243959988794354530763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94162162639992529569687175 141243243959988794354530763)
            ·
              refine ⟨211864865939983191531796145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141243243959988794354530763 211864865939983191531796145)
              ·
                refine ⟨158898649454987393648847109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211864865939983191531796145 158898649454987393648847109)
                ·
                  refine ⟨29793496772810136309158833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158898649454987393648847109 29793496772810136309158833)
                  ·
                    refine ⟨22345122579607602231869125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29793496772810136309158833 22345122579607602231869125)
                    ·
                      refine ⟨4189710483676425418475461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22345122579607602231869125 4189710483676425418475461)
                      ·
                        rfl

theorem cell23_8159432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_8159432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159432 prefixEnd_8159432 := by exact prefixLift 8159432
  have htrace : WordTrace (prefixWord ++ tailWord_8159432) baseStart_8159432 baseEnd_8159432 := by
    simpa [prefixWord, tailWord_8159432, baseEnd_8159432] using wordTrace_append hprefix tailTrace_8159432
  have hstable : (prefixWord ++ tailWord_8159432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159432).length < 2 ^ (prefixWord ++ tailWord_8159432).sum := by decide
  have hdescent : baseEnd_8159432 < baseStart_8159432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159472 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_8159472 : Nat := 118140960795 + 8159472 * 2 ^ 59
def prefixEnd_8159472 : Nat := 4983230072969 + 3 ^ 40 * 8159472 * 2
def baseEnd_8159472 : Nat := 1396577007634201753991759

theorem tailTrace_8159472 : CollatzResearch.WordTrace tailWord_8159472 prefixEnd_8159472 1396577007634201753991759 := by
  unfold tailWord_8159472
  simp only [CollatzResearch.WordTrace]
  refine ⟨148800196347816972859184335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198400261797089297145579113 148800196347816972859184335)
  ·
    refine ⟨223200294521725459288776503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148800196347816972859184335 223200294521725459288776503)
    ·
      refine ⟨334800441782588188933164755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223200294521725459288776503 334800441782588188933164755)
      ·
        refine ⟨502200662673882283399747133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334800441782588188933164755 502200662673882283399747133)
        ·
          refine ⟨188325248502705856274905175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502200662673882283399747133 188325248502705856274905175)
          ·
            refine ⟨282487872754058784412357763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188325248502705856274905175 282487872754058784412357763)
            ·
              refine ⟨423731809131088176618536645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282487872754058784412357763 423731809131088176618536645)
              ·
                refine ⟨79449714212079033115975621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423731809131088176618536645 79449714212079033115975621)
                ·
                  refine ⟨14896821414764818709245429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79449714212079033115975621 14896821414764818709245429)
                  ·
                    refine ⟨1396577007634201753991759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14896821414764818709245429 1396577007634201753991759)
                    ·
                      rfl

theorem cell23_8159472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_8159472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159472 prefixEnd_8159472 := by exact prefixLift 8159472
  have htrace : WordTrace (prefixWord ++ tailWord_8159472) baseStart_8159472 baseEnd_8159472 := by
    simpa [prefixWord, tailWord_8159472, baseEnd_8159472] using wordTrace_append hprefix tailTrace_8159472
  have hstable : (prefixWord ++ tailWord_8159472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159472).length < 2 ^ (prefixWord ++ tailWord_8159472).sum := by decide
  have hdescent : baseEnd_8159472 < baseStart_8159472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159509 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_8159509 : Nat := 118140960795 + 8159509 * 2 ^ 59
def prefixEnd_8159509 : Nat := 4983230072969 + 3 ^ 40 * 8159509 * 2
def baseEnd_8159509 : Nat := 4189750021686821617212607

theorem tailTrace_8159509 : CollatzResearch.WordTrace tailWord_8159509 prefixEnd_8159509 4189750021686821617212607 := by
  unfold tailWord_8159509
  simp only [CollatzResearch.WordTrace]
  refine ⟨297601742196499901037465581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198401161464333267358310387 297601742196499901037465581)
  ·
    refine ⟨111600653323687462889049593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297601742196499901037465581 111600653323687462889049593)
    ·
      refine ⟨83700489992765597166787195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111600653323687462889049593 83700489992765597166787195)
      ·
        refine ⟨125550734989148395750180793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83700489992765597166787195 125550734989148395750180793)
        ·
          refine ⟨94163051241861296812635595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125550734989148395750180793 94163051241861296812635595)
          ·
            refine ⟨141244576862791945218953393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94163051241861296812635595 141244576862791945218953393)
            ·
              refine ⟨105933432647093958914215045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141244576862791945218953393 105933432647093958914215045)
              ·
                refine ⟨19862518621330117296415321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105933432647093958914215045 19862518621330117296415321)
                ·
                  refine ⟨14896888965997587972311491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19862518621330117296415321 14896888965997587972311491)
                  ·
                    refine ⟨22345333448996381958467237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14896888965997587972311491 22345333448996381958467237)
                    ·
                      refine ⟨4189750021686821617212607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22345333448996381958467237 4189750021686821617212607)
                      ·
                        rfl

theorem cell23_8159509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_8159509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159509 prefixEnd_8159509 := by exact prefixLift 8159509
  have htrace : WordTrace (prefixWord ++ tailWord_8159509) baseStart_8159509 baseEnd_8159509 := by
    simpa [prefixWord, tailWord_8159509, baseEnd_8159509] using wordTrace_append hprefix tailTrace_8159509
  have hstable : (prefixWord ++ tailWord_8159509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159509).length < 2 ^ (prefixWord ++ tailWord_8159509).sum := by decide
  have hdescent : baseEnd_8159509 < baseStart_8159509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159552 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_8159552 : Nat := 118140960795 + 8159552 * 2 ^ 59
def prefixEnd_8159552 : Nat := 4983230072969 + 3 ^ 40 * 8159552 * 2
def baseEnd_8159552 : Nat := 4189772101354964948974909

theorem tailTrace_8159552 : CollatzResearch.WordTrace tailWord_8159552 prefixEnd_8159552 4189772101354964948974909 := by
  unfold tailWord_8159552
  simp only [CollatzResearch.WordTrace]
  refine ⟨148801655267672059690640455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198402207023562746254187273 148801655267672059690640455)
  ·
    refine ⟨223202482901508089535960683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148801655267672059690640455 223202482901508089535960683)
    ·
      refine ⟨334803724352262134303941025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223202482901508089535960683 334803724352262134303941025)
      ·
        refine ⟨251102793264196600727955769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334803724352262134303941025 251102793264196600727955769)
        ·
          refine ⟨188327094948147450545966827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251102793264196600727955769 188327094948147450545966827)
          ·
            refine ⟨282490642422221175818950241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188327094948147450545966827 282490642422221175818950241)
            ·
              refine ⟨211867981816665881864212681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282490642422221175818950241 211867981816665881864212681)
              ·
                refine ⟨158900986362499411398159511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211867981816665881864212681 158900986362499411398159511)
                ·
                  refine ⟨238351479543749117097239267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158900986362499411398159511 238351479543749117097239267)
                  ·
                    refine ⟨357527219315623675645858901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238351479543749117097239267 357527219315623675645858901)
                    ·
                      refine ⟨4189772101354964948974909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357527219315623675645858901 4189772101354964948974909)
                      ·
                        rfl

theorem cell23_8159552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_8159552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159552 prefixEnd_8159552 := by exact prefixLift 8159552
  have htrace : WordTrace (prefixWord ++ tailWord_8159552) baseStart_8159552 baseEnd_8159552 := by
    simpa [prefixWord, tailWord_8159552, baseEnd_8159552] using wordTrace_append hprefix tailTrace_8159552
  have hstable : (prefixWord ++ tailWord_8159552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159552).length < 2 ^ (prefixWord ++ tailWord_8159552).sum := by decide
  have hdescent : baseEnd_8159552 < baseStart_8159552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159576 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_8159576 : Nat := 118140960795 + 8159576 * 2 ^ 59
def prefixEnd_8159576 : Nat := 4983230072969 + 3 ^ 40 * 8159576 * 2
def baseEnd_8159576 : Nat := 4189784424890672855074799

theorem tailTrace_8159576 : CollatzResearch.WordTrace tailWord_8159576 prefixEnd_8159576 4189784424890672855074799 := by
  unfold tailWord_8159576
  simp only [CollatzResearch.WordTrace]
  refine ⟨148802092943628585740077291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198402790591504780986769721 148802092943628585740077291)
  ·
    refine ⟨223203139415442878610115937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148802092943628585740077291 223203139415442878610115937)
    ·
      refine ⟨167402354561582158957586953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223203139415442878610115937 167402354561582158957586953)
      ·
        refine ⟨125551765921186619218190215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167402354561582158957586953 125551765921186619218190215)
        ·
          refine ⟨188327648881779928827285323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125551765921186619218190215 188327648881779928827285323)
          ·
            refine ⟨282491473322669893240927985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188327648881779928827285323 282491473322669893240927985)
            ·
              refine ⟨211868604992002419930695989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282491473322669893240927985 211868604992002419930695989)
              ·
                refine ⟨19862681718000226868502749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211868604992002419930695989 19862681718000226868502749)
                ·
                  refine ⟨7448505644250085075688531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19862681718000226868502749 7448505644250085075688531)
                  ·
                    refine ⟨11172758466375127613532797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7448505644250085075688531 11172758466375127613532797)
                    ·
                      refine ⟨4189784424890672855074799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11172758466375127613532797 4189784424890672855074799)
                      ·
                        rfl

theorem cell23_8159576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_8159576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159576 prefixEnd_8159576 := by exact prefixLift 8159576
  have htrace : WordTrace (prefixWord ++ tailWord_8159576) baseStart_8159576 baseEnd_8159576 := by
    simpa [prefixWord, tailWord_8159576, baseEnd_8159576] using wordTrace_append hprefix tailTrace_8159576
  have hstable : (prefixWord ++ tailWord_8159576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159576).length < 2 ^ (prefixWord ++ tailWord_8159576).sum := by decide
  have hdescent : baseEnd_8159576 < baseStart_8159576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159596 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_8159596 : Nat := 118140960795 + 8159596 * 2 ^ 59
def prefixEnd_8159596 : Nat := 4983230072969 + 3 ^ 40 * 8159596 * 2
def baseEnd_8159596 : Nat := 1396598231501254258941569

theorem tailTrace_8159596 : CollatzResearch.WordTrace tailWord_8159596 prefixEnd_8159596 1396598231501254258941569 := by
  unfold tailWord_8159596
  simp only [CollatzResearch.WordTrace]
  refine ⟨148802457673592357447941321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198403276898123143263921761 148802457673592357447941321)
  ·
    refine ⟨111601843255194268085955991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148802457673592357447941321 111601843255194268085955991)
    ·
      refine ⟨167402764882791402128933987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111601843255194268085955991 167402764882791402128933987)
      ·
        refine ⟨251104147324187103193400981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167402764882791402128933987 251104147324187103193400981)
        ·
          refine ⟨11770506905821270462190671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251104147324187103193400981 11770506905821270462190671)
          ·
            refine ⟨17655760358731905693286007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11770506905821270462190671 17655760358731905693286007)
            ·
              refine ⟨26483640538097858539929011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17655760358731905693286007 26483640538097858539929011)
              ·
                refine ⟨39725460807146787809893517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26483640538097858539929011 39725460807146787809893517)
                ·
                  refine ⟨14897047802680045428710069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39725460807146787809893517 14897047802680045428710069)
                  ·
                    refine ⟨1396598231501254258941569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14897047802680045428710069 1396598231501254258941569)
                    ·
                      rfl

theorem cell23_8159596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_8159596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159596 prefixEnd_8159596 := by exact prefixLift 8159596
  have htrace : WordTrace (prefixWord ++ tailWord_8159596) baseStart_8159596 baseEnd_8159596 := by
    simpa [prefixWord, tailWord_8159596, baseEnd_8159596] using wordTrace_append hprefix tailTrace_8159596
  have hstable : (prefixWord ++ tailWord_8159596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159596).length < 2 ^ (prefixWord ++ tailWord_8159596).sum := by decide
  have hdescent : baseEnd_8159596 < baseStart_8159596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159613 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_8159613 : Nat := 118140960795 + 8159613 * 2 ^ 59
def prefixEnd_8159613 : Nat := 4983230072969 + 3 ^ 40 * 8159613 * 2
def baseEnd_8159613 : Nat := 1396601141224963070104043

theorem tailTrace_8159613 : CollatzResearch.WordTrace tailWord_8159613 prefixEnd_8159613 1396601141224963070104043 := by
  unfold tailWord_8159613
  simp only [CollatzResearch.WordTrace]
  refine ⟨297605535388123126799251493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198403690258748751199500995 297605535388123126799251493)
  ·
    refine ⟨55801037885273086274859655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297605535388123126799251493 55801037885273086274859655)
    ·
      refine ⟨83701556827909629412289483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55801037885273086274859655 83701556827909629412289483)
      ·
        refine ⟨125552335241864444118434225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83701556827909629412289483 125552335241864444118434225)
        ·
          refine ⟨94164251431398333088825669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125552335241864444118434225 94164251431398333088825669)
          ·
            refine ⟨17655797143387187454154813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94164251431398333088825669 17655797143387187454154813)
            ·
              refine ⟨6620923928770195295308055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17655797143387187454154813 6620923928770195295308055)
              ·
                refine ⟨9931385893155292942962083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620923928770195295308055 9931385893155292942962083)
                ·
                  refine ⟨14897078839732939414443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931385893155292942962083 14897078839732939414443125)
                  ·
                    refine ⟨1396601141224963070104043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14897078839732939414443125 1396601141224963070104043)
                    ·
                      rfl

theorem cell23_8159613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_8159613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159613 prefixEnd_8159613 := by exact prefixLift 8159613
  have htrace : WordTrace (prefixWord ++ tailWord_8159613) baseStart_8159613 baseEnd_8159613 := by
    simpa [prefixWord, tailWord_8159613, baseEnd_8159613] using wordTrace_append hprefix tailTrace_8159613
  have hstable : (prefixWord ++ tailWord_8159613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159613).length < 2 ^ (prefixWord ++ tailWord_8159613).sum := by decide
  have hdescent : baseEnd_8159613 < baseStart_8159613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159627 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 1, 1, 3]
def baseStart_8159627 : Nat := 118140960795 + 8159627 * 2 ^ 59
def prefixEnd_8159627 : Nat := 4983230072969 + 3 ^ 40 * 8159627 * 2
def baseEnd_8159627 : Nat := 4189810612404052155537065

theorem tailTrace_8159627 : CollatzResearch.WordTrace tailWord_8159627 prefixEnd_8159627 4189810612404052155537065 := by
  unfold tailWord_8159627
  simp only [CollatzResearch.WordTrace]
  refine ⟨297606046010072407190261135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198404030673381604793507423 297606046010072407190261135)
  ·
    refine ⟨446409069015108610785391703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297606046010072407190261135 446409069015108610785391703)
    ·
      refine ⟨669613603522662916178087555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446409069015108610785391703 669613603522662916178087555)
      ·
        refine ⟨1004420405283994374267131333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669613603522662916178087555 1004420405283994374267131333)
        ·
          refine ⟨188328825990748945175087125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1004420405283994374267131333 188328825990748945175087125)
          ·
            refine ⟨8827913718316356805082209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188328825990748945175087125 8827913718316356805082209)
            ·
              refine ⟨6620935288737267603811657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8827913718316356805082209 6620935288737267603811657)
              ·
                refine ⟨4965701466552950702858743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6620935288737267603811657 4965701466552950702858743)
                ·
                  refine ⟨7448552199829426054288115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965701466552950702858743 7448552199829426054288115)
                  ·
                    refine ⟨11172828299744139081432173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7448552199829426054288115 11172828299744139081432173)
                    ·
                      refine ⟨4189810612404052155537065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11172828299744139081432173 4189810612404052155537065)
                      ·
                        rfl

theorem cell23_8159627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 1, 3].length) (baseStart_8159627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159627 prefixEnd_8159627 := by exact prefixLift 8159627
  have htrace : WordTrace (prefixWord ++ tailWord_8159627) baseStart_8159627 baseEnd_8159627 := by
    simpa [prefixWord, tailWord_8159627, baseEnd_8159627] using wordTrace_append hprefix tailTrace_8159627
  have hstable : (prefixWord ++ tailWord_8159627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159627).length < 2 ^ (prefixWord ++ tailWord_8159627).sum := by decide
  have hdescent : baseEnd_8159627 < baseStart_8159627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159639 : List Nat := [1, 1, 3, 3, 1, 1, 5, 8]
def baseStart_8159639 : Nat := 118140960795 + 8159639 * 2 ^ 59
def prefixEnd_8159639 : Nat := 4983230072969 + 3 ^ 40 * 8159639 * 2
def baseEnd_8159639 : Nat := 155178399043403929947667

theorem tailTrace_8159639 : CollatzResearch.WordTrace tailWord_8159639 prefixEnd_8159639 155178399043403929947667 := by
  unfold tailWord_8159639
  simp only [CollatzResearch.WordTrace]
  refine ⟨297606483686028933239697971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198404322457352622159798647 297606483686028933239697971)
  ·
    refine ⟨446409725529043399859546957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297606483686028933239697971 446409725529043399859546957)
    ·
      refine ⟨167403647073391274947330109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446409725529043399859546957 167403647073391274947330109)
      ·
        refine ⟨62776367652521728105248791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167403647073391274947330109 62776367652521728105248791)
        ·
          refine ⟨94164551478782592157873187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62776367652521728105248791 94164551478782592157873187)
          ·
            refine ⟨141246827218173888236809781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94164551478782592157873187 141246827218173888236809781)
            ·
              refine ⟨13241890051703802022200917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141246827218173888236809781 13241890051703802022200917)
              ·
                refine ⟨155178399043403929947667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13241890051703802022200917 155178399043403929947667)
                ·
                  rfl

theorem cell23_8159639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 8].length) (baseStart_8159639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159639 prefixEnd_8159639 := by exact prefixLift 8159639
  have htrace : WordTrace (prefixWord ++ tailWord_8159639) baseStart_8159639 baseEnd_8159639 := by
    simpa [prefixWord, tailWord_8159639, baseEnd_8159639] using wordTrace_append hprefix tailTrace_8159639
  have hstable : (prefixWord ++ tailWord_8159639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159639).length < 2 ^ (prefixWord ++ tailWord_8159639).sum := by decide
  have hdescent : baseEnd_8159639 < baseStart_8159639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159650 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_8159650 : Nat := 118140960795 + 8159650 * 2 ^ 59
def prefixEnd_8159650 : Nat := 4983230072969 + 3 ^ 40 * 8159650 * 2
def baseEnd_8159650 : Nat := 4189822422459105565549459

theorem tailTrace_8159650 : CollatzResearch.WordTrace tailWord_8159650 prefixEnd_8159650 4189822422459105565549459 := by
  unfold tailWord_8159650
  simp only [CollatzResearch.WordTrace]
  refine ⟨74401721222247270529587101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198404589925992721412232269 74401721222247270529587101)
  ·
    refine ⟨27900645458342726448595163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74401721222247270529587101 27900645458342726448595163)
    ·
      refine ⟨41850968187514089672892745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27900645458342726448595163 41850968187514089672892745)
      ·
        refine ⟨31388226140635567254669559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41850968187514089672892745 31388226140635567254669559)
        ·
          refine ⟨47082339210953350882004339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31388226140635567254669559 47082339210953350882004339)
          ·
            refine ⟨70623508816430026323006509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47082339210953350882004339 70623508816430026323006509)
            ·
              refine ⟨26483815806161259871127441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70623508816430026323006509 26483815806161259871127441)
              ·
                refine ⟨19862861854620944903345581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26483815806161259871127441 19862861854620944903345581)
                ·
                  refine ⟨7448573195482854338754593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19862861854620944903345581 7448573195482854338754593)
                  ·
                    refine ⟨5586429896612140754065945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448573195482854338754593 5586429896612140754065945)
                    ·
                      refine ⟨4189822422459105565549459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586429896612140754065945 4189822422459105565549459)
                      ·
                        rfl

theorem cell23_8159650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_8159650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159650 prefixEnd_8159650 := by exact prefixLift 8159650
  have htrace : WordTrace (prefixWord ++ tailWord_8159650) baseStart_8159650 baseEnd_8159650 := by
    simpa [prefixWord, tailWord_8159650, baseEnd_8159650] using wordTrace_append hprefix tailTrace_8159650
  have hstable : (prefixWord ++ tailWord_8159650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159650).length < 2 ^ (prefixWord ++ tailWord_8159650).sum := by decide
  have hdescent : baseEnd_8159650 < baseStart_8159650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159666 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_8159666 : Nat := 118140960795 + 8159666 * 2 ^ 59
def prefixEnd_8159666 : Nat := 4983230072969 + 3 ^ 40 * 8159666 * 2
def baseEnd_8159666 : Nat := 4189830638149577502949385

theorem tailTrace_8159666 : CollatzResearch.WordTrace tailWord_8159666 prefixEnd_8159666 4189830638149577502949385 := by
  unfold tailWord_8159666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74401867114232779212732713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198404978971287411233953901 74401867114232779212732713)
  ·
    refine ⟨55801400335674584409549535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74401867114232779212732713 55801400335674584409549535)
    ·
      refine ⟨83702100503511876614324303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55801400335674584409549535 83702100503511876614324303)
      ·
        refine ⟨125553150755267814921486455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83702100503511876614324303 125553150755267814921486455)
        ·
          refine ⟨188329726132901722382229683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125553150755267814921486455 188329726132901722382229683)
          ·
            refine ⟨282494589199352583573344525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188329726132901722382229683 282494589199352583573344525)
            ·
              refine ⟨105935470949757218840004197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282494589199352583573344525 105935470949757218840004197)
              ·
                refine ⟨19862900803079478532500787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105935470949757218840004197 19862900803079478532500787)
                ·
                  refine ⟨29794351204619217798751181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19862900803079478532500787 29794351204619217798751181)
                  ·
                    refine ⟨11172881701732206674531693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29794351204619217798751181 11172881701732206674531693)
                    ·
                      refine ⟨4189830638149577502949385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11172881701732206674531693 4189830638149577502949385)
                      ·
                        rfl

theorem cell23_8159666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_8159666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159666 prefixEnd_8159666 := by exact prefixLift 8159666
  have htrace : WordTrace (prefixWord ++ tailWord_8159666) baseStart_8159666 baseEnd_8159666 := by
    simpa [prefixWord, tailWord_8159666, baseEnd_8159666] using wordTrace_append hprefix tailTrace_8159666
  have hstable : (prefixWord ++ tailWord_8159666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159666).length < 2 ^ (prefixWord ++ tailWord_8159666).sum := by decide
  have hdescent : baseEnd_8159666 < baseStart_8159666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159689 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_8159689 : Nat := 118140960795 + 8159689 * 2 ^ 59
def prefixEnd_8159689 : Nat := 4983230072969 + 3 ^ 40 * 8159689 * 2
def baseEnd_8159689 : Nat := 4189842448204630912961779

theorem tailTrace_8159689 : CollatzResearch.WordTrace tailWord_8159689 prefixEnd_8159689 4189842448204630912961779 := by
  unfold tailWord_8159689
  simp only [CollatzResearch.WordTrace]
  refine ⟨297608307335847791779018121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198405538223898527852678747 297608307335847791779018121)
  ·
    refine ⟨223206230501885843834263591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297608307335847791779018121 223206230501885843834263591)
    ·
      refine ⟨334809345752828765751395387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223206230501885843834263591 334809345752828765751395387)
      ·
        refine ⟨502214018629243148627093081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334809345752828765751395387 502214018629243148627093081)
        ·
          refine ⟨376660513971932361470319811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502214018629243148627093081 376660513971932361470319811)
          ·
            refine ⟨564990770957898542205479717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376660513971932361470319811 564990770957898542205479717)
            ·
              refine ⟨105935769554605976663527447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564990770957898542205479717 105935769554605976663527447)
              ·
                refine ⟨158903654331908964995291171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105935769554605976663527447 158903654331908964995291171)
                ·
                  refine ⟨238355481497863447492936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158903654331908964995291171 238355481497863447492936757)
                  ·
                    refine ⟨22345826390424698202462821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 238355481497863447492936757 22345826390424698202462821)
                    ·
                      refine ⟨4189842448204630912961779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22345826390424698202462821 4189842448204630912961779)
                      ·
                        rfl

theorem cell23_8159689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_8159689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159689 prefixEnd_8159689 := by exact prefixLift 8159689
  have htrace : WordTrace (prefixWord ++ tailWord_8159689) baseStart_8159689 baseEnd_8159689 := by
    simpa [prefixWord, tailWord_8159689, baseEnd_8159689] using wordTrace_append hprefix tailTrace_8159689
  have hstable : (prefixWord ++ tailWord_8159689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159689).length < 2 ^ (prefixWord ++ tailWord_8159689).sum := by decide
  have hdescent : baseEnd_8159689 < baseStart_8159689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159700 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_8159700 : Nat := 118140960795 + 8159700 * 2 ^ 59
def prefixEnd_8159700 : Nat := 4983230072969 + 3 ^ 40 * 8159700 * 2
def baseEnd_8159700 : Nat := 4189848096491830369924229

theorem tailTrace_8159700 : CollatzResearch.WordTrace tailWord_8159700 prefixEnd_8159700 4189848096491830369924229 := by
  unfold tailWord_8159700
  simp only [CollatzResearch.WordTrace]
  refine ⟨148804354269403970328834277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198405805692538627105112369 148804354269403970328834277)
  ·
    refine ⟨27900816425513244436656427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148804354269403970328834277 27900816425513244436656427)
    ·
      refine ⟨41851224638269866654984641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27900816425513244436656427 41851224638269866654984641)
      ·
        refine ⟨31388418478702399991238481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41851224638269866654984641 31388418478702399991238481)
        ·
          refine ⟨23541313859026799993428861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31388418478702399991238481 23541313859026799993428861)
          ·
            refine ⟨8827992697135049997535823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23541313859026799993428861 8827992697135049997535823)
            ·
              refine ⟨13241989045702574996303735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827992697135049997535823 13241989045702574996303735)
              ·
                refine ⟨19862983568553862494455603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13241989045702574996303735 19862983568553862494455603)
                ·
                  refine ⟨29794475352830793741683405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19862983568553862494455603 29794475352830793741683405)
                  ·
                    refine ⟨11172928257311547653131277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29794475352830793741683405 11172928257311547653131277)
                    ·
                      refine ⟨4189848096491830369924229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11172928257311547653131277 4189848096491830369924229)
                      ·
                        rfl

theorem cell23_8159700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_8159700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159700 prefixEnd_8159700 := by exact prefixLift 8159700
  have htrace : WordTrace (prefixWord ++ tailWord_8159700) baseStart_8159700 baseEnd_8159700 := by
    simpa [prefixWord, tailWord_8159700, baseEnd_8159700] using wordTrace_append hprefix tailTrace_8159700
  have hstable : (prefixWord ++ tailWord_8159700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159700).length < 2 ^ (prefixWord ++ tailWord_8159700).sum := by decide
  have hdescent : baseEnd_8159700 < baseStart_8159700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159723 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 6, 2, 2]
def baseStart_8159723 : Nat := 118140960795 + 8159723 * 2 ^ 59
def prefixEnd_8159723 : Nat := 4983230072969 + 3 ^ 40 * 8159723 * 2
def baseEnd_8159723 : Nat := 4189859906546883779936623

theorem tailTrace_8159723 : CollatzResearch.WordTrace tailWord_8159723 prefixEnd_8159723 4189859906546883779936623 := by
  unfold tailWord_8159723
  simp only [CollatzResearch.WordTrace]
  refine ⟨297609547417724615585755823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198406364945149743723837215 297609547417724615585755823)
  ·
    refine ⟨446414321126586923378633735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297609547417724615585755823 446414321126586923378633735)
    ·
      refine ⟨669621481689880385067950603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446414321126586923378633735 669621481689880385067950603)
      ·
        refine ⟨1004432222534820577601925905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669621481689880385067950603 1004432222534820577601925905)
        ·
          refine ⟨753324166901115433201444429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004432222534820577601925905 753324166901115433201444429)
          ·
            refine ⟨282496562587918287450541661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 753324166901115433201444429 282496562587918287450541661)
            ·
              refine ⟨105936210970469357793953123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282496562587918287450541661 105936210970469357793953123)
              ·
                refine ⟨158904316455704036690929685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105936210970469357793953123 158904316455704036690929685)
                ·
                  refine ⟨7448639833861126719887329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158904316455704036690929685 7448639833861126719887329)
                  ·
                    refine ⟨5586479875395845039915497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448639833861126719887329 5586479875395845039915497)
                    ·
                      refine ⟨4189859906546883779936623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586479875395845039915497 4189859906546883779936623)
                      ·
                        rfl

theorem cell23_8159723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 2, 2].length) (baseStart_8159723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159723 prefixEnd_8159723 := by exact prefixLift 8159723
  have htrace : WordTrace (prefixWord ++ tailWord_8159723) baseStart_8159723 baseEnd_8159723 := by
    simpa [prefixWord, tailWord_8159723, baseEnd_8159723] using wordTrace_append hprefix tailTrace_8159723
  have hstable : (prefixWord ++ tailWord_8159723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159723).length < 2 ^ (prefixWord ++ tailWord_8159723).sum := by decide
  have hdescent : baseEnd_8159723 < baseStart_8159723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159726 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_8159726 : Nat := 118140960795 + 8159726 * 2 ^ 59
def prefixEnd_8159726 : Nat := 4983230072969 + 3 ^ 40 * 8159726 * 2
def baseEnd_8159726 : Nat := 4189861446988847268199109

theorem tailTrace_8159726 : CollatzResearch.WordTrace tailWord_8159726 prefixEnd_8159726 4189861446988847268199109 := by
  unfold tailWord_8159726
  simp only [CollatzResearch.WordTrace]
  refine ⟨37201207104589218387264379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198406437891142498065410021 37201207104589218387264379)
  ·
    refine ⟨55801810656883827580896569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37201207104589218387264379 55801810656883827580896569)
    ·
      refine ⟨41851357992662870685672427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55801810656883827580896569 41851357992662870685672427)
      ·
        refine ⟨62777036988994306028508641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41851357992662870685672427 62777036988994306028508641)
        ·
          refine ⟨47082777741745729521381481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62777036988994306028508641 47082777741745729521381481)
          ·
            refine ⟨35312083306309297141036111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47082777741745729521381481 35312083306309297141036111)
            ·
              refine ⟨52968124959463945711554167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35312083306309297141036111 52968124959463945711554167)
              ·
                refine ⟨79452187439195918567331251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52968124959463945711554167 79452187439195918567331251)
                ·
                  refine ⟨119178281158793877850996877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79452187439195918567331251 119178281158793877850996877)
                  ·
                    refine ⟨44691855434547704194123829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119178281158793877850996877 44691855434547704194123829)
                    ·
                      refine ⟨4189861446988847268199109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44691855434547704194123829 4189861446988847268199109)
                      ·
                        rfl

theorem cell23_8159726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_8159726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159726 prefixEnd_8159726 := by exact prefixLift 8159726
  have htrace : WordTrace (prefixWord ++ tailWord_8159726) baseStart_8159726 baseEnd_8159726 := by
    simpa [prefixWord, tailWord_8159726, baseEnd_8159726] using wordTrace_append hprefix tailTrace_8159726
  have hstable : (prefixWord ++ tailWord_8159726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159726).length < 2 ^ (prefixWord ++ tailWord_8159726).sum := by decide
  have hdescent : baseEnd_8159726 < baseStart_8159726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159740 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_8159740 : Nat := 118140960795 + 8159740 * 2 ^ 59
def prefixEnd_8159740 : Nat := 4983230072969 + 3 ^ 40 * 8159740 * 2
def baseEnd_8159740 : Nat := 4189868635718010213424045

theorem tailTrace_8159740 : CollatzResearch.WordTrace tailWord_8159740 prefixEnd_8159740 4189868635718010213424045 := by
  unfold tailWord_8159740
  simp only [CollatzResearch.WordTrace]
  refine ⟨148805083729331513744562337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198406778305775351659416449 148805083729331513744562337)
  ·
    refine ⟨111603812796998635308421753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148805083729331513744562337 111603812796998635308421753)
    ·
      refine ⟨83702859597748976481316315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111603812796998635308421753 83702859597748976481316315)
      ·
        refine ⟨125554289396623464721974473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83702859597748976481316315 125554289396623464721974473)
        ·
          refine ⟨94165717047467598541480855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125554289396623464721974473 94165717047467598541480855)
          ·
            refine ⟨141248575571201397812221283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94165717047467598541480855 141248575571201397812221283)
            ·
              refine ⟨211872863356802096718331925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141248575571201397812221283 211872863356802096718331925)
              ·
                refine ⟨9931540469850098283671809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211872863356802096718331925 9931540469850098283671809)
                ·
                  refine ⟨7448655352387573712753857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9931540469850098283671809 7448655352387573712753857)
                  ·
                    refine ⟨5586491514290680284565393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448655352387573712753857 5586491514290680284565393)
                    ·
                      refine ⟨4189868635718010213424045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586491514290680284565393 4189868635718010213424045)
                      ·
                        rfl

theorem cell23_8159740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_8159740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159740 prefixEnd_8159740 := by exact prefixLift 8159740
  have htrace : WordTrace (prefixWord ++ tailWord_8159740) baseStart_8159740 baseEnd_8159740 := by
    simpa [prefixWord, tailWord_8159740, baseEnd_8159740] using wordTrace_append hprefix tailTrace_8159740
  have hstable : (prefixWord ++ tailWord_8159740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159740).length < 2 ^ (prefixWord ++ tailWord_8159740).sum := by decide
  have hdescent : baseEnd_8159740 < baseStart_8159740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159813 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 6, 2]
def baseStart_8159813 : Nat := 118140960795 + 8159813 * 2 ^ 59
def prefixEnd_8159813 : Nat := 4983230072969 + 3 ^ 40 * 8159813 * 2
def baseEnd_8159813 : Nat := 4189906119805788427811209

theorem tailTrace_8159813 : CollatzResearch.WordTrace tailWord_8159813 prefixEnd_8159813 4189906119805788427811209 := by
  unfold tailWord_8159813
  simp only [CollatzResearch.WordTrace]
  refine ⟨297612829987398560956532093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198408553324932373971021395 297612829987398560956532093)
  ·
    refine ⟨111604811245274460358699535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297612829987398560956532093 111604811245274460358699535)
    ·
      refine ⟨167407216867911690538049303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111604811245274460358699535 167407216867911690538049303)
      ·
        refine ⟨251110825301867535807073955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167407216867911690538049303 251110825301867535807073955)
        ·
          refine ⟨376666237952801303710610933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251110825301867535807073955 376666237952801303710610933)
          ·
            refine ⟨35312459808075122222869775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376666237952801303710610933 35312459808075122222869775)
            ·
              refine ⟨52968689712112683334304663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35312459808075122222869775 52968689712112683334304663)
              ·
                refine ⟨79453034568169025001456995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52968689712112683334304663 79453034568169025001456995)
                ·
                  refine ⟨119179551852253537502185493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79453034568169025001456995 119179551852253537502185493)
                  ·
                    refine ⟨5586541493074384570414945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119179551852253537502185493 5586541493074384570414945)
                    ·
                      refine ⟨4189906119805788427811209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586541493074384570414945 4189906119805788427811209)
                      ·
                        rfl

theorem cell23_8159813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_8159813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159813 prefixEnd_8159813 := by exact prefixLift 8159813
  have htrace : WordTrace (prefixWord ++ tailWord_8159813) baseStart_8159813 baseEnd_8159813 := by
    simpa [prefixWord, tailWord_8159813, baseEnd_8159813] using wordTrace_append hprefix tailTrace_8159813
  have hstable : (prefixWord ++ tailWord_8159813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159813).length < 2 ^ (prefixWord ++ tailWord_8159813).sum := by decide
  have hdescent : baseEnd_8159813 < baseStart_8159813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159840 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 1, 4]
def baseStart_8159840 : Nat := 118140960795 + 8159840 * 2 ^ 59
def prefixEnd_8159840 : Nat := 4983230072969 + 3 ^ 40 * 8159840 * 2
def baseEnd_8159840 : Nat := 1396639994594486607391195

theorem tailTrace_8159840 : CollatzResearch.WordTrace tailWord_8159840 prefixEnd_8159840 1396639994594486607391195 := by
  unfold tailWord_8159840
  simp only [CollatzResearch.WordTrace]
  refine ⟨148806907379150372283882487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198409209838867163045176649 148806907379150372283882487)
  ·
    refine ⟨223210361068725558425823731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148806907379150372283882487 223210361068725558425823731)
    ·
      refine ⟨334815541603088337638735597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223210361068725558425823731 334815541603088337638735597)
      ·
        refine ⟨125555828101158126614525849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334815541603088337638735597 125555828101158126614525849)
        ·
          refine ⟨94166871075868594960894387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125555828101158126614525849 94166871075868594960894387)
          ·
            refine ⟨141250306613802892441341581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94166871075868594960894387 141250306613802892441341581)
            ·
              refine ⟨52968864980176084665503093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141250306613802892441341581 52968864980176084665503093)
              ·
                refine ⟨4965831091891507937390915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52968864980176084665503093 4965831091891507937390915)
                ·
                  refine ⟨7448746637837261906086373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965831091891507937390915 7448746637837261906086373)
                  ·
                    refine ⟨1396639994594486607391195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448746637837261906086373 1396639994594486607391195)
                    ·
                      rfl

theorem cell23_8159840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 4].length) (baseStart_8159840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159840 prefixEnd_8159840 := by exact prefixLift 8159840
  have htrace : WordTrace (prefixWord ++ tailWord_8159840) baseStart_8159840 baseEnd_8159840 := by
    simpa [prefixWord, tailWord_8159840, baseEnd_8159840] using wordTrace_append hprefix tailTrace_8159840
  have hstable : (prefixWord ++ tailWord_8159840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159840).length < 2 ^ (prefixWord ++ tailWord_8159840).sum := by decide
  have hdescent : baseEnd_8159840 < baseStart_8159840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159853 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 8]
def baseStart_8159853 : Nat := 118140960795 + 8159853 * 2 ^ 59
def prefixEnd_8159853 : Nat := 4983230072969 + 3 ^ 40 * 8159853 * 2
def baseEnd_8159853 : Nat := 465547406559107585701225

theorem tailTrace_8159853 : CollatzResearch.WordTrace tailWord_8159853 prefixEnd_8159853 465547406559107585701225 := by
  unfold tailWord_8159853
  simp only [CollatzResearch.WordTrace]
  refine ⟨297614288907253647787988213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198409525938169098525325475 297614288907253647787988213)
  ·
    refine ⟨27901339585055029480123895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297614288907253647787988213 27901339585055029480123895)
    ·
      refine ⟨41852009377582544220185843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27901339585055029480123895 41852009377582544220185843)
      ·
        refine ⟨62778014066373816330278765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41852009377582544220185843 62778014066373816330278765)
        ·
          refine ⟨23541755274890181123854537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62778014066373816330278765 23541755274890181123854537)
          ·
            refine ⟨17656316456167635842890903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23541755274890181123854537 17656316456167635842890903)
            ·
              refine ⟨26484474684251453764336355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656316456167635842890903 26484474684251453764336355)
              ·
                refine ⟨39726712026377180646504533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26484474684251453764336355 39726712026377180646504533)
                ·
                  refine ⟨465547406559107585701225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39726712026377180646504533 465547406559107585701225)
                  ·
                    rfl

theorem cell23_8159853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_8159853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159853 prefixEnd_8159853 := by exact prefixLift 8159853
  have htrace : WordTrace (prefixWord ++ tailWord_8159853) baseStart_8159853 baseEnd_8159853 := by
    simpa [prefixWord, tailWord_8159853, baseEnd_8159853] using wordTrace_append hprefix tailTrace_8159853
  have hstable : (prefixWord ++ tailWord_8159853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159853).length < 2 ^ (prefixWord ++ tailWord_8159853).sum := by decide
  have hdescent : baseEnd_8159853 < baseStart_8159853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159900 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_8159900 : Nat := 118140960795 + 8159900 * 2 ^ 59
def prefixEnd_8159900 : Nat := 4983230072969 + 3 ^ 40 * 8159900 * 2
def baseEnd_8159900 : Nat := 1396650264207576529141103

theorem tailTrace_8159900 : CollatzResearch.WordTrace tailWord_8159900 prefixEnd_8159900 1396650264207576529141103 := by
  unfold tailWord_8159900
  simp only [CollatzResearch.WordTrace]
  refine ⟨148808001569041687407474577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198410668758722249876632769 148808001569041687407474577)
  ·
    refine ⟨111606001176781265555605933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148808001569041687407474577 111606001176781265555605933)
    ·
      refine ⟨41852250441292974583352225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111606001176781265555605933 41852250441292974583352225)
      ·
        refine ⟨31389187830969730937514169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41852250441292974583352225 31389187830969730937514169)
        ·
          refine ⟨23541890873227298203135627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31389187830969730937514169 23541890873227298203135627)
          ·
            refine ⟨35312836309840947304703441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23541890873227298203135627 35312836309840947304703441)
            ·
              refine ⟨26484627232380710478527581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35312836309840947304703441 26484627232380710478527581)
              ·
                refine ⟨9931735212142766429447843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26484627232380710478527581 9931735212142766429447843)
                ·
                  refine ⟨14897602818214149644171765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931735212142766429447843 14897602818214149644171765)
                  ·
                    refine ⟨1396650264207576529141103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14897602818214149644171765 1396650264207576529141103)
                    ·
                      rfl

theorem cell23_8159900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_8159900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159900 prefixEnd_8159900 := by exact prefixLift 8159900
  have htrace : WordTrace (prefixWord ++ tailWord_8159900) baseStart_8159900 baseEnd_8159900 := by
    simpa [prefixWord, tailWord_8159900, baseEnd_8159900] using wordTrace_append hprefix tailTrace_8159900
  have hstable : (prefixWord ++ tailWord_8159900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159900).length < 2 ^ (prefixWord ++ tailWord_8159900).sum := by decide
  have hdescent : baseEnd_8159900 < baseStart_8159900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159923 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5]
def baseStart_8159923 : Nat := 118140960795 + 8159923 * 2 ^ 59
def prefixEnd_8159923 : Nat := 4983230072969 + 3 ^ 40 * 8159923 * 2
def baseEnd_8159923 : Nat := 4189962602677782997435703

theorem tailTrace_8159923 : CollatzResearch.WordTrace tailWord_8159923 prefixEnd_8159923 4189962602677782997435703 := by
  unfold tailWord_8159923
  simp only [CollatzResearch.WordTrace]
  refine ⟨297616842017000049743036423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198411228011333366495357615 297616842017000049743036423)
  ·
    refine ⟨446425263025500074614554635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297616842017000049743036423 446425263025500074614554635)
    ·
      refine ⟨669637894538250111921831953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446425263025500074614554635 669637894538250111921831953)
      ·
        refine ⟨502228420903687583941373965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669637894538250111921831953 502228420903687583941373965)
        ·
          refine ⟨188335657838882843978015237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502228420903687583941373965 188335657838882843978015237)
          ·
            refine ⟨35312935844790533245877857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188335657838882843978015237 35312935844790533245877857)
            ·
              refine ⟨26484701883592899934408393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35312935844790533245877857 26484701883592899934408393)
              ·
                refine ⟨19863526412694674950806295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26484701883592899934408393 19863526412694674950806295)
                ·
                  refine ⟨29795289619042012426209443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19863526412694674950806295 29795289619042012426209443)
                  ·
                    refine ⟨44692934428563018639314165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29795289619042012426209443 44692934428563018639314165)
                    ·
                      refine ⟨4189962602677782997435703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44692934428563018639314165 4189962602677782997435703)
                      ·
                        rfl

theorem cell23_8159923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_8159923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159923 prefixEnd_8159923 := by exact prefixLift 8159923
  have htrace : WordTrace (prefixWord ++ tailWord_8159923) baseStart_8159923 baseEnd_8159923 := by
    simpa [prefixWord, tailWord_8159923, baseEnd_8159923] using wordTrace_append hprefix tailTrace_8159923
  have hstable : (prefixWord ++ tailWord_8159923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159923).length < 2 ^ (prefixWord ++ tailWord_8159923).sum := by decide
  have hdescent : baseEnd_8159923 < baseStart_8159923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159930 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_8159930 : Nat := 118140960795 + 8159930 * 2 ^ 59
def prefixEnd_8159930 : Nat := 4983230072969 + 3 ^ 40 * 8159930 * 2
def baseEnd_8159930 : Nat := 1396655399014121490016057

theorem tailTrace_8159930 : CollatzResearch.WordTrace tailWord_8159930 prefixEnd_8159930 1396655399014121490016057 := by
  unfold tailWord_8159930
  simp only [CollatzResearch.WordTrace]
  refine ⟨74404274331993672484635311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198411398218649793292360829 74404274331993672484635311)
  ·
    refine ⟨111606411497990508726952967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74404274331993672484635311 111606411497990508726952967)
    ·
      refine ⟨167409617246985763090429451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111606411497990508726952967 167409617246985763090429451)
      ·
        refine ⟨251114425870478644635644177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167409617246985763090429451 251114425870478644635644177)
        ·
          refine ⟨188335819402858983476733133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251114425870478644635644177 188335819402858983476733133)
          ·
            refine ⟨70625932276072118803774925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188335819402858983476733133 70625932276072118803774925)
            ·
              refine ⟨26484724603527044551415597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70625932276072118803774925 26484724603527044551415597)
              ·
                refine ⟨9931771726322641706780849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26484724603527044551415597 9931771726322641706780849)
                ·
                  refine ⟨7448828794741981280085637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9931771726322641706780849 7448828794741981280085637)
                  ·
                    refine ⟨1396655399014121490016057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448828794741981280085637 1396655399014121490016057)
                    ·
                      rfl

theorem cell23_8159930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_8159930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159930 prefixEnd_8159930 := by exact prefixLift 8159930
  have htrace : WordTrace (prefixWord ++ tailWord_8159930) baseStart_8159930 baseEnd_8159930 := by
    simpa [prefixWord, tailWord_8159930, baseEnd_8159930] using wordTrace_append hprefix tailTrace_8159930
  have hstable : (prefixWord ++ tailWord_8159930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159930).length < 2 ^ (prefixWord ++ tailWord_8159930).sum := by decide
  have hdescent : baseEnd_8159930 < baseStart_8159930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159933 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_8159933 : Nat := 118140960795 + 8159933 * 2 ^ 59
def prefixEnd_8159933 : Nat := 4983230072969 + 3 ^ 40 * 8159933 * 2
def baseEnd_8159933 : Nat := 4189967737484327958310657

theorem tailTrace_8159933 : CollatzResearch.WordTrace tailWord_8159933 prefixEnd_8159933 4189967737484327958310657 := by
  unfold tailWord_8159933
  simp only [CollatzResearch.WordTrace]
  refine ⟨297617206746963821450900453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198411471164642547633933635 297617206746963821450900453)
  ·
    refine ⟨55803226265055716522043835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297617206746963821450900453 55803226265055716522043835)
    ·
      refine ⟨83704839397583574783065753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55803226265055716522043835 83704839397583574783065753)
      ·
        refine ⟨62778629548187681087299315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83704839397583574783065753 62778629548187681087299315)
        ·
          refine ⟨94167944322281521630948973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62778629548187681087299315 94167944322281521630948973)
          ·
            refine ⟨35312979120855570611605865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94167944322281521630948973 35312979120855570611605865)
            ·
              refine ⟨26484734340641677958704399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35312979120855570611605865 26484734340641677958704399)
              ·
                refine ⟨39727101510962516938056599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26484734340641677958704399 39727101510962516938056599)
                ·
                  refine ⟨59590652266443775407084899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39727101510962516938056599 59590652266443775407084899)
                  ·
                    refine ⟨89385978399665663110627349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59590652266443775407084899 89385978399665663110627349)
                    ·
                      refine ⟨4189967737484327958310657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89385978399665663110627349 4189967737484327958310657)
                      ·
                        rfl

theorem cell23_8159933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_8159933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159933 prefixEnd_8159933 := by exact prefixLift 8159933
  have htrace : WordTrace (prefixWord ++ tailWord_8159933) baseStart_8159933 baseEnd_8159933 := by
    simpa [prefixWord, tailWord_8159933, baseEnd_8159933] using wordTrace_append hprefix tailTrace_8159933
  have hstable : (prefixWord ++ tailWord_8159933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159933).length < 2 ^ (prefixWord ++ tailWord_8159933).sum := by decide
  have hdescent : baseEnd_8159933 < baseStart_8159933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159950 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_8159950 : Nat := 118140960795 + 8159950 * 2 ^ 59
def prefixEnd_8159950 : Nat := 4983230072969 + 3 ^ 40 * 8159950 * 2
def baseEnd_8159950 : Nat := 4189976466655454391798079

theorem tailTrace_8159950 : CollatzResearch.WordTrace tailWord_8159950 prefixEnd_8159950 4189976466655454391798079 := by
  unfold tailWord_8159950
  simp only [CollatzResearch.WordTrace]
  refine ⟨37202228348487779169283663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198411884525268155569512869 37202228348487779169283663)
  ·
    refine ⟨55803342522731668753925495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37202228348487779169283663 55803342522731668753925495)
    ·
      refine ⟨83705013784097503130888243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55803342522731668753925495 83705013784097503130888243)
      ·
        refine ⟨125557520676146254696332365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83705013784097503130888243 125557520676146254696332365)
        ·
          refine ⟨47084070253554845511124637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125557520676146254696332365 47084070253554845511124637)
          ·
            refine ⟨17656526345083067066671739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47084070253554845511124637 17656526345083067066671739)
            ·
              refine ⟨26484789517624600600007609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656526345083067066671739 26484789517624600600007609)
              ·
                refine ⟨19863592138218450450005707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26484789517624600600007609 19863592138218450450005707)
                ·
                  refine ⟨29795388207327675675008561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19863592138218450450005707 29795388207327675675008561)
                  ·
                    refine ⟨22346541155495756756256421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29795388207327675675008561 22346541155495756756256421)
                    ·
                      refine ⟨4189976466655454391798079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22346541155495756756256421 4189976466655454391798079)
                      ·
                        rfl

theorem cell23_8159950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_8159950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159950 prefixEnd_8159950 := by exact prefixLift 8159950
  have htrace : WordTrace (prefixWord ++ tailWord_8159950) baseStart_8159950 baseEnd_8159950 := by
    simpa [prefixWord, tailWord_8159950, baseEnd_8159950] using wordTrace_append hprefix tailTrace_8159950
  have hstable : (prefixWord ++ tailWord_8159950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159950).length < 2 ^ (prefixWord ++ tailWord_8159950).sum := by decide
  have hdescent : baseEnd_8159950 < baseStart_8159950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159954 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_8159954 : Nat := 118140960795 + 8159954 * 2 ^ 59
def prefixEnd_8159954 : Nat := 4983230072969 + 3 ^ 40 * 8159954 * 2
def baseEnd_8159954 : Nat := 4189978520578072376148061

theorem tailTrace_8159954 : CollatzResearch.WordTrace tailWord_8159954 prefixEnd_8159954 4189978520578072376148061 := by
  unfold tailWord_8159954
  simp only [CollatzResearch.WordTrace]
  refine ⟨74404493169971935509353729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198411981786591828024943277 74404493169971935509353729)
  ·
    refine ⟨55803369877478951632015297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74404493169971935509353729 55803369877478951632015297)
    ·
      refine ⟨41852527408109213724011473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55803369877478951632015297 41852527408109213724011473)
      ·
        refine ⟨31389395556081910293008605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41852527408109213724011473 31389395556081910293008605)
        ·
          refine ⟨11771023333530716359878227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31389395556081910293008605 11771023333530716359878227)
          ·
            refine ⟨17656535000296074539817341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771023333530716359878227 17656535000296074539817341)
            ·
              refine ⟨6621200625111027952431503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17656535000296074539817341 6621200625111027952431503)
              ·
                refine ⟨9931800937666541928647255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621200625111027952431503 9931800937666541928647255)
                ·
                  refine ⟨14897701406499812892970883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931800937666541928647255 14897701406499812892970883)
                  ·
                    refine ⟨22346552109749719339456325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14897701406499812892970883 22346552109749719339456325)
                    ·
                      refine ⟨4189978520578072376148061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22346552109749719339456325 4189978520578072376148061)
                      ·
                        rfl

theorem cell23_8159954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_8159954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159954 prefixEnd_8159954 := by exact prefixLift 8159954
  have htrace : WordTrace (prefixWord ++ tailWord_8159954) baseStart_8159954 baseEnd_8159954 := by
    simpa [prefixWord, tailWord_8159954, baseEnd_8159954] using wordTrace_append hprefix tailTrace_8159954
  have hstable : (prefixWord ++ tailWord_8159954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159954).length < 2 ^ (prefixWord ++ tailWord_8159954).sum := by decide
  have hdescent : baseEnd_8159954 < baseStart_8159954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159964 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_8159964 : Nat := 118140960795 + 8159964 * 2 ^ 59
def prefixEnd_8159964 : Nat := 4983230072969 + 3 ^ 40 * 8159964 * 2
def baseEnd_8159964 : Nat := 1396661218461539112341005

theorem tailTrace_8159964 : CollatzResearch.WordTrace tailWord_8159964 prefixEnd_8159964 1396661218461539112341005 := by
  unfold tailWord_8159964
  simp only [CollatzResearch.WordTrace]
  refine ⟨148809168704925756872639473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198412224939901009163519297 148809168704925756872639473)
  ·
    refine ⟨111606876528694317654479605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148809168704925756872639473 111606876528694317654479605)
    ·
      refine ⟨10463144674565092280107463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111606876528694317654479605 10463144674565092280107463)
      ·
        refine ⟨15694717011847638420161195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10463144674565092280107463 15694717011847638420161195)
        ·
          refine ⟨23542075517771457630241793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694717011847638420161195 23542075517771457630241793)
          ·
            refine ⟨17656556638328593222681345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23542075517771457630241793 17656556638328593222681345)
            ·
              refine ⟨13242417478746444917011009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17656556638328593222681345 13242417478746444917011009)
              ·
                refine ⟨9931813109059833687758257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13242417478746444917011009 9931813109059833687758257)
                ·
                  refine ⟨7448859831794875265818693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9931813109059833687758257 7448859831794875265818693)
                  ·
                    refine ⟨1396661218461539112341005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448859831794875265818693 1396661218461539112341005)
                    ·
                      rfl

theorem cell23_8159964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_8159964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159964 prefixEnd_8159964 := by exact prefixLift 8159964
  have htrace : WordTrace (prefixWord ++ tailWord_8159964) baseStart_8159964 baseEnd_8159964 := by
    simpa [prefixWord, tailWord_8159964, baseEnd_8159964] using wordTrace_append hprefix tailTrace_8159964
  have hstable : (prefixWord ++ tailWord_8159964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159964).length < 2 ^ (prefixWord ++ tailWord_8159964).sum := by decide
  have hdescent : baseEnd_8159964 < baseStart_8159964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159971 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 1, 2, 2]
def baseStart_8159971 : Nat := 118140960795 + 8159971 * 2 ^ 59
def prefixEnd_8159971 : Nat := 4983230072969 + 3 ^ 40 * 8159971 * 2
def baseEnd_8159971 : Nat := 4189987249749198809635483

theorem tailTrace_8159971 : CollatzResearch.WordTrace tailWord_8159971 prefixEnd_8159971 4189987249749198809635483 := by
  unfold tailWord_8159971
  simp only [CollatzResearch.WordTrace]
  refine ⟨297618592720826153940783767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198412395147217435960522511 297618592720826153940783767)
  ·
    refine ⟨446427889081239230911175651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297618592720826153940783767 446427889081239230911175651)
    ·
      refine ⟨669641833621858846366763477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446427889081239230911175651 669641833621858846366763477)
      ·
        refine ⟨15694730475512316711721019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 669641833621858846366763477 15694730475512316711721019)
        ·
          refine ⟨23542095713268475067581529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694730475512316711721019 23542095713268475067581529)
          ·
            refine ⟨17656571784951356300686147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23542095713268475067581529 17656571784951356300686147)
            ·
              refine ⟨26484857677427034451029221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656571784951356300686147 26484857677427034451029221)
              ·
                refine ⟨4965910814517568959567979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26484857677427034451029221 4965910814517568959567979)
                ·
                  refine ⟨7448866221776353439351969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965910814517568959567979 7448866221776353439351969)
                  ·
                    refine ⟨5586649666332265079513977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448866221776353439351969 5586649666332265079513977)
                    ·
                      refine ⟨4189987249749198809635483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586649666332265079513977 4189987249749198809635483)
                      ·
                        rfl

theorem cell23_8159971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_8159971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159971 prefixEnd_8159971 := by exact prefixLift 8159971
  have htrace : WordTrace (prefixWord ++ tailWord_8159971) baseStart_8159971 baseEnd_8159971 := by
    simpa [prefixWord, tailWord_8159971, baseEnd_8159971] using wordTrace_append hprefix tailTrace_8159971
  have hstable : (prefixWord ++ tailWord_8159971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159971).length < 2 ^ (prefixWord ++ tailWord_8159971).sum := by decide
  have hdescent : baseEnd_8159971 < baseStart_8159971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159973 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_8159973 : Nat := 118140960795 + 8159973 * 2 ^ 59
def prefixEnd_8159973 : Nat := 4983230072969 + 3 ^ 40 * 8159973 * 2
def baseEnd_8159973 : Nat := 1396662758903502600603491

theorem tailTrace_8159973 : CollatzResearch.WordTrace tailWord_8159973 prefixEnd_8159973 1396662758903502600603491 := by
  unfold tailWord_8159973
  simp only [CollatzResearch.WordTrace]
  refine ⟨297618665666818908282356573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198412443777879272188237715 297618665666818908282356573)
  ·
    refine ⟨111606999625057090605883715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297618665666818908282356573 111606999625057090605883715)
    ·
      refine ⟨167410499437585635908825573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111606999625057090605883715 167410499437585635908825573)
      ·
        refine ⟨31389468644547306732904795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167410499437585635908825573 31389468644547306732904795)
        ·
          refine ⟨47084202966820960099357193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31389468644547306732904795 47084202966820960099357193)
          ·
            refine ⟨35313152225115720074517895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47084202966820960099357193 35313152225115720074517895)
            ·
              refine ⟨52969728337673580111776843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35313152225115720074517895 52969728337673580111776843)
              ·
                refine ⟨79454592506510370167665265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52969728337673580111776843 79454592506510370167665265)
                ·
                  refine ⟨59590944379882777625748949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79454592506510370167665265 59590944379882777625748949)
                  ·
                    refine ⟨1396662758903502600603491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59590944379882777625748949 1396662758903502600603491)
                    ·
                      rfl

theorem cell23_8159973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_8159973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159973 prefixEnd_8159973 := by exact prefixLift 8159973
  have htrace : WordTrace (prefixWord ++ tailWord_8159973) baseStart_8159973 baseEnd_8159973 := by
    simpa [prefixWord, tailWord_8159973, baseEnd_8159973] using wordTrace_append hprefix tailTrace_8159973
  have hstable : (prefixWord ++ tailWord_8159973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159973).length < 2 ^ (prefixWord ++ tailWord_8159973).sum := by decide
  have hdescent : baseEnd_8159973 < baseStart_8159973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159988 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_8159988 : Nat := 118140960795 + 8159988 * 2 ^ 59
def prefixEnd_8159988 : Nat := 4983230072969 + 3 ^ 40 * 8159988 * 2
def baseEnd_8159988 : Nat := 4189995978920325243122905

theorem tailTrace_8159988 : CollatzResearch.WordTrace tailWord_8159988 prefixEnd_8159988 4189995978920325243122905 := by
  unfold tailWord_8159988
  simp only [CollatzResearch.WordTrace]
  refine ⟨148809606380882282922076309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198412808507843043896101745 148809606380882282922076309)
  ·
    refine ⟨6975450299103857011972327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148809606380882282922076309 6975450299103857011972327)
    ·
      refine ⟨10463175448655785517958491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975450299103857011972327 10463175448655785517958491)
      ·
        refine ⟨15694763172983678276937737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10463175448655785517958491 15694763172983678276937737)
        ·
          refine ⟨11771072379737758707703303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15694763172983678276937737 11771072379737758707703303)
          ·
            refine ⟨17656608569606638061554955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771072379737758707703303 17656608569606638061554955)
            ·
              refine ⟨26484912854409957092332433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656608569606638061554955 26484912854409957092332433)
              ·
                refine ⟨19863684640807467819249325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26484912854409957092332433 19863684640807467819249325)
                ·
                  refine ⟨7448881740302800432218497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19863684640807467819249325 7448881740302800432218497)
                  ·
                    refine ⟨5586661305227100324163873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448881740302800432218497 5586661305227100324163873)
                    ·
                      refine ⟨4189995978920325243122905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586661305227100324163873 4189995978920325243122905)
                      ·
                        rfl

theorem cell23_8159988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_8159988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159988 prefixEnd_8159988 := by exact prefixLift 8159988
  have htrace : WordTrace (prefixWord ++ tailWord_8159988) baseStart_8159988 baseEnd_8159988 := by
    simpa [prefixWord, tailWord_8159988, baseEnd_8159988] using wordTrace_append hprefix tailTrace_8159988
  have hstable : (prefixWord ++ tailWord_8159988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159988).length < 2 ^ (prefixWord ++ tailWord_8159988).sum := by decide
  have hdescent : baseEnd_8159988 < baseStart_8159988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8159997 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_8159997 : Nat := 118140960795 + 8159997 * 2 ^ 59
def prefixEnd_8159997 : Nat := 4983230072969 + 3 ^ 40 * 8159997 * 2
def baseEnd_8159997 : Nat := 4190000600246215707910363

theorem tailTrace_8159997 : CollatzResearch.WordTrace tailWord_8159997 prefixEnd_8159997 4190000600246215707910363 := by
  unfold tailWord_8159997
  simp only [CollatzResearch.WordTrace]
  refine ⟨297619541018731960381230245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198413027345821306920820163 297619541018731960381230245)
  ·
    refine ⟨55803663941012242571480671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297619541018731960381230245 55803663941012242571480671)
    ·
      refine ⟨83705495911518363857221007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55803663941012242571480671 83705495911518363857221007)
      ·
        refine ⟨125558243867277545785831511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83705495911518363857221007 125558243867277545785831511)
        ·
          refine ⟨188337365800916318678747267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125558243867277545785831511 188337365800916318678747267)
          ·
            refine ⟨282506048701374478018120901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188337365800916318678747267 282506048701374478018120901)
            ·
              refine ⟨52969884131507714628397669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282506048701374478018120901 52969884131507714628397669)
              ·
                refine ⟨9931853274657696492824563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52969884131507714628397669 9931853274657696492824563)
                ·
                  refine ⟨14897779911986544739236845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931853274657696492824563 14897779911986544739236845)
                  ·
                    refine ⟨5586667466994954277213817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14897779911986544739236845 5586667466994954277213817)
                    ·
                      refine ⟨4190000600246215707910363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586667466994954277213817 4190000600246215707910363)
                      ·
                        rfl

theorem cell23_8159997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_8159997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8159997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8159997 prefixEnd_8159997 := by exact prefixLift 8159997
  have htrace : WordTrace (prefixWord ++ tailWord_8159997) baseStart_8159997 baseEnd_8159997 := by
    simpa [prefixWord, tailWord_8159997, baseEnd_8159997] using wordTrace_append hprefix tailTrace_8159997
  have hstable : (prefixWord ++ tailWord_8159997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8159997).length < 2 ^ (prefixWord ++ tailWord_8159997).sum := by decide
  have hdescent : baseEnd_8159997 < baseStart_8159997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8159997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160040 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_8160040 : Nat := 118140960795 + 8160040 * 2 ^ 59
def prefixEnd_8160040 : Nat := 4983230072969 + 3 ^ 40 * 8160040 * 2
def baseEnd_8160040 : Nat := 4190022679914359039672665

theorem tailTrace_8160040 : CollatzResearch.WordTrace tailWord_8160040 prefixEnd_8160040 4190022679914359039672665 := by
  unfold tailWord_8160040
  simp only [CollatzResearch.WordTrace]
  refine ⟨148810554678788089362522787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198414072905050785816697049 148810554678788089362522787)
  ·
    refine ⟨223215832018182134043784181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148810554678788089362522787 223215832018182134043784181)
    ·
      refine ⟨20926484251704575066604767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223215832018182134043784181 20926484251704575066604767)
      ·
        refine ⟨31389726377556862599907151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20926484251704575066604767 31389726377556862599907151)
        ·
          refine ⟨47084589566335293899860727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31389726377556862599907151 47084589566335293899860727)
          ·
            refine ⟨70626884349502940849791091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47084589566335293899860727 70626884349502940849791091)
            ·
              refine ⟨105940326524254411274686637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70626884349502940849791091 105940326524254411274686637)
              ·
                refine ⟨39727622446595404228007489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105940326524254411274686637 39727622446595404228007489)
                ·
                  refine ⟨29795716834946553171005617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39727622446595404228007489 29795716834946553171005617)
                  ·
                    refine ⟨22346787626209914878254213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29795716834946553171005617 22346787626209914878254213)
                    ·
                      refine ⟨4190022679914359039672665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22346787626209914878254213 4190022679914359039672665)
                      ·
                        rfl

theorem cell23_8160040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_8160040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160040 prefixEnd_8160040 := by exact prefixLift 8160040
  have htrace : WordTrace (prefixWord ++ tailWord_8160040) baseStart_8160040 baseEnd_8160040 := by
    simpa [prefixWord, tailWord_8160040, baseEnd_8160040] using wordTrace_append hprefix tailTrace_8160040
  have hstable : (prefixWord ++ tailWord_8160040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160040).length < 2 ^ (prefixWord ++ tailWord_8160040).sum := by decide
  have hdescent : baseEnd_8160040 < baseStart_8160040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160084 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 7]
def baseStart_8160084 : Nat := 118140960795 + 8160084 * 2 ^ 59
def prefixEnd_8160084 : Nat := 4983230072969 + 3 ^ 40 * 8160084 * 2
def baseEnd_8160084 : Nat := 465560585895906318613607

theorem tailTrace_8160084 : CollatzResearch.WordTrace tailWord_8160084 prefixEnd_8160084 465560585895906318613607 := by
  unfold tailWord_8160084
  simp only [CollatzResearch.WordTrace]
  refine ⟨148811357084708387119823653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198415142779611182826431537 148811357084708387119823653)
  ·
    refine ⟨27902129453382822584966935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148811357084708387119823653 27902129453382822584966935)
    ·
      refine ⟨41853194180074233877450403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27902129453382822584966935 41853194180074233877450403)
      ·
        refine ⟨62779791270111350816175605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41853194180074233877450403 62779791270111350816175605)
        ·
          refine ⟨5885605431572939139016463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62779791270111350816175605 5885605431572939139016463)
          ·
            refine ⟨8828408147359408708524695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885605431572939139016463 8828408147359408708524695)
            ·
              refine ⟨13242612221039113062787043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828408147359408708524695 13242612221039113062787043)
              ·
                refine ⟨19863918331558669594180565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13242612221039113062787043 19863918331558669594180565)
                ·
                  refine ⟨465560585895906318613607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19863918331558669594180565 465560585895906318613607)
                  ·
                    rfl

theorem cell23_8160084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_8160084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160084 prefixEnd_8160084 := by exact prefixLift 8160084
  have htrace : WordTrace (prefixWord ++ tailWord_8160084) baseStart_8160084 baseEnd_8160084 := by
    simpa [prefixWord, tailWord_8160084, baseEnd_8160084] using wordTrace_append hprefix tailTrace_8160084
  have hstable : (prefixWord ++ tailWord_8160084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160084).length < 2 ^ (prefixWord ++ tailWord_8160084).sum := by decide
  have hdescent : baseEnd_8160084 < baseStart_8160084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160090 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_8160090 : Nat := 118140960795 + 8160090 * 2 ^ 59
def prefixEnd_8160090 : Nat := 4983230072969 + 3 ^ 40 * 8160090 * 2
def baseEnd_8160090 : Nat := 4190048353947083844047435

theorem tailTrace_8160090 : CollatzResearch.WordTrace tailWord_8160090 prefixEnd_8160090 4190048353947083844047435 := by
  unfold tailWord_8160090
  simp only [CollatzResearch.WordTrace]
  refine ⟨74405733251848759316091431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198415288671596691509577149 74405733251848759316091431)
  ·
    refine ⟨111608599877773138974137147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74405733251848759316091431 111608599877773138974137147)
    ·
      refine ⟨167412899816659708461205721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111608599877773138974137147 167412899816659708461205721)
      ·
        refine ⟨125559674862494781345904291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167412899816659708461205721 125559674862494781345904291)
        ·
          refine ⟨188339512293742172018856437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125559674862494781345904291 188339512293742172018856437)
          ·
            refine ⟨17656829277538328626767791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188339512293742172018856437 17656829277538328626767791)
            ·
              refine ⟨26485243916307492940151687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656829277538328626767791 26485243916307492940151687)
              ·
                refine ⟨39727865874461239410227531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26485243916307492940151687 39727865874461239410227531)
                ·
                  refine ⟨59591798811691859115341297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39727865874461239410227531 59591798811691859115341297)
                  ·
                    refine ⟨44693849108768894336505973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59591798811691859115341297 44693849108768894336505973)
                    ·
                      refine ⟨4190048353947083844047435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44693849108768894336505973 4190048353947083844047435)
                      ·
                        rfl

theorem cell23_8160090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_8160090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160090 prefixEnd_8160090 := by exact prefixLift 8160090
  have htrace : WordTrace (prefixWord ++ tailWord_8160090) baseStart_8160090 baseEnd_8160090 := by
    simpa [prefixWord, tailWord_8160090, baseEnd_8160090] using wordTrace_append hprefix tailTrace_8160090
  have hstable : (prefixWord ++ tailWord_8160090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160090).length < 2 ^ (prefixWord ++ tailWord_8160090).sum := by decide
  have hdescent : baseEnd_8160090 < baseStart_8160090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160117 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_8160117 : Nat := 118140960795 + 8160117 * 2 ^ 59
def prefixEnd_8160117 : Nat := 4983230072969 + 3 ^ 40 * 8160117 * 2
def baseEnd_8160117 : Nat := 4190062217924755238409811

theorem tailTrace_8160117 : CollatzResearch.WordTrace tailWord_8160117 prefixEnd_8160117 4190062217924755238409811 := by
  unfold tailWord_8160117
  simp only [CollatzResearch.WordTrace]
  refine ⟨297623917778297220875598605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198415945185531480583732403 297623917778297220875598605)
  ·
    refine ⟨111608969166861457828349477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297623917778297220875598605 111608969166861457828349477)
    ·
      refine ⟨20926681718786523342815527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111608969166861457828349477 20926681718786523342815527)
      ·
        refine ⟨31390022578179785014223291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20926681718786523342815527 31390022578179785014223291)
        ·
          refine ⟨47085033867269677521334937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31390022578179785014223291 47085033867269677521334937)
          ·
            refine ⟨35313775400452258141001203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47085033867269677521334937 35313775400452258141001203)
            ·
              refine ⟨52970663100678387211501805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35313775400452258141001203 52970663100678387211501805)
              ·
                refine ⟨19863998662754395204313177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52970663100678387211501805 19863998662754395204313177)
                ·
                  refine ⟨14897998997065796403234883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19863998662754395204313177 14897998997065796403234883)
                  ·
                    refine ⟨22346998495598694604852325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14897998997065796403234883 22346998495598694604852325)
                    ·
                      refine ⟨4190062217924755238409811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22346998495598694604852325 4190062217924755238409811)
                      ·
                        rfl

theorem cell23_8160117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_8160117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160117 prefixEnd_8160117 := by exact prefixLift 8160117
  have htrace : WordTrace (prefixWord ++ tailWord_8160117) baseStart_8160117 baseEnd_8160117 := by
    simpa [prefixWord, tailWord_8160117, baseEnd_8160117] using wordTrace_append hprefix tailTrace_8160117
  have hstable : (prefixWord ++ tailWord_8160117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160117).length < 2 ^ (prefixWord ++ tailWord_8160117).sum := by decide
  have hdescent : baseEnd_8160117 < baseStart_8160117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160123 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 10]
def baseStart_8160123 : Nat := 118140960795 + 8160123 * 2 ^ 59
def prefixEnd_8160123 : Nat := 4983230072969 + 3 ^ 40 * 8160123 * 2
def baseEnd_8160123 : Nat := 465562810978742468326087

theorem tailTrace_8160123 : CollatzResearch.WordTrace tailWord_8160123 prefixEnd_8160123 465562810978742468326087 := by
  unfold tailWord_8160123
  simp only [CollatzResearch.WordTrace]
  refine ⟨297624136616275483900317023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198416091077516989266878015 297624136616275483900317023)
  ·
    refine ⟨446436204924413225850475535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297624136616275483900317023 446436204924413225850475535)
    ·
      refine ⟨669654307386619838775713303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446436204924413225850475535 669654307386619838775713303)
      ·
        refine ⟨1004481461079929758163569955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669654307386619838775713303 1004481461079929758163569955)
        ·
          refine ⟨1506722191619894637245354933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004481461079929758163569955 1506722191619894637245354933)
          ·
            refine ⟨141255205464365122241752025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1506722191619894637245354933 141255205464365122241752025)
            ·
              refine ⟨105941404098273841681314019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141255205464365122241752025 105941404098273841681314019)
              ·
                refine ⟨158912106147410762521971029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105941404098273841681314019 158912106147410762521971029)
                ·
                  refine ⟨465562810978742468326087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 158912106147410762521971029 465562810978742468326087)
                  ·
                    rfl

theorem cell23_8160123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 10].length) (baseStart_8160123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160123 prefixEnd_8160123 := by exact prefixLift 8160123
  have htrace : WordTrace (prefixWord ++ tailWord_8160123) baseStart_8160123 baseEnd_8160123 := by
    simpa [prefixWord, tailWord_8160123, baseEnd_8160123] using wordTrace_append hprefix tailTrace_8160123
  have hstable : (prefixWord ++ tailWord_8160123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160123).length < 2 ^ (prefixWord ++ tailWord_8160123).sum := by decide
  have hdescent : baseEnd_8160123 < baseStart_8160123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160137 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_8160137 : Nat := 118140960795 + 8160137 * 2 ^ 59
def prefixEnd_8160137 : Nat := 4983230072969 + 3 ^ 40 * 8160137 * 2
def baseEnd_8160137 : Nat := 4190072487537845160159719

theorem tailTrace_8160137 : CollatzResearch.WordTrace tailWord_8160137 prefixEnd_8160137 4190072487537845160159719 := by
  unfold tailWord_8160137
  simp only [CollatzResearch.WordTrace]
  refine ⟨297624647238224764291326665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198416431492149842860884443 297624647238224764291326665)
  ·
    refine ⟨223218485428668573218494999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297624647238224764291326665 223218485428668573218494999)
    ·
      refine ⟨334827728143002859827742499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223218485428668573218494999 334827728143002859827742499)
      ·
        refine ⟨502241592214504289741613749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334827728143002859827742499 502241592214504289741613749)
        ·
          refine ⟨47085149270109777163276289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502241592214504289741613749 47085149270109777163276289)
          ·
            refine ⟨35313861952582332872457217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47085149270109777163276289 35313861952582332872457217)
            ·
              refine ⟨26485396464436749654342913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35313861952582332872457217 26485396464436749654342913)
              ·
                refine ⟨19864047348327562240757185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26485396464436749654342913 19864047348327562240757185)
                ·
                  refine ⟨14898035511245671680567889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19864047348327562240757185 14898035511245671680567889)
                  ·
                    refine ⟨11173526633434253760425917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14898035511245671680567889 11173526633434253760425917)
                    ·
                      refine ⟨4190072487537845160159719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11173526633434253760425917 4190072487537845160159719)
                      ·
                        rfl

theorem cell23_8160137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_8160137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160137 prefixEnd_8160137 := by exact prefixLift 8160137
  have htrace : WordTrace (prefixWord ++ tailWord_8160137) baseStart_8160137 baseEnd_8160137 := by
    simpa [prefixWord, tailWord_8160137, baseEnd_8160137] using wordTrace_append hprefix tailTrace_8160137
  have hstable : (prefixWord ++ tailWord_8160137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160137).length < 2 ^ (prefixWord ++ tailWord_8160137).sum := by decide
  have hdescent : baseEnd_8160137 < baseStart_8160137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160140 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 6]
def baseStart_8160140 : Nat := 118140960795 + 8160140 * 2 ^ 59
def prefixEnd_8160140 : Nat := 4983230072969 + 3 ^ 40 * 8160140 * 2
def baseEnd_8160140 : Nat := 465563780886645405380245

theorem tailTrace_8160140 : CollatzResearch.WordTrace tailWord_8160140 prefixEnd_8160140 465563780886645405380245 := by
  unfold tailWord_8160140
  simp only [CollatzResearch.WordTrace]
  refine ⟨148812378328606947901842937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198416504438142597202457249 148812378328606947901842937)
  ·
    refine ⟨111609283746455210926382203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148812378328606947901842937 111609283746455210926382203)
    ·
      refine ⟨167413925619682816389573305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111609283746455210926382203 167413925619682816389573305)
      ·
        refine ⟨125560444214762112292179979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167413925619682816389573305 125560444214762112292179979)
        ·
          refine ⟨188340666322143168438269969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125560444214762112292179979 188340666322143168438269969)
          ·
            refine ⟨141255499741607376328702477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188340666322143168438269969 141255499741607376328702477)
            ·
              refine ⟨52970812403102766123263429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141255499741607376328702477 52970812403102766123263429)
              ·
                refine ⟨9932027325581768648111893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52970812403102766123263429 9932027325581768648111893)
                ·
                  refine ⟨465563780886645405380245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9932027325581768648111893 465563780886645405380245)
                  ·
                    rfl

theorem cell23_8160140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_8160140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160140 prefixEnd_8160140 := by exact prefixLift 8160140
  have htrace : WordTrace (prefixWord ++ tailWord_8160140) baseStart_8160140 baseEnd_8160140 := by
    simpa [prefixWord, tailWord_8160140, baseEnd_8160140] using wordTrace_append hprefix tailTrace_8160140
  have hstable : (prefixWord ++ tailWord_8160140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160140).length < 2 ^ (prefixWord ++ tailWord_8160140).sum := by decide
  have hdescent : baseEnd_8160140 < baseStart_8160140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160217 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 1, 6]
def baseStart_8160217 : Nat := 118140960795 + 8160217 * 2 ^ 59
def prefixEnd_8160217 : Nat := 4983230072969 + 3 ^ 40 * 8160217 * 2
def baseEnd_8160217 : Nat := 1396704521996734949053117

theorem tailTrace_8160217 : CollatzResearch.WordTrace tailWord_8160217 prefixEnd_8160217 1396704521996734949053117 := by
  unfold tailWord_8160217
  simp only [CollatzResearch.WordTrace]
  refine ⟨297627565077934937954238905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198418376718623291969492603 297627565077934937954238905)
  ·
    refine ⟨223220673808451203465679179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297627565077934937954238905 223220673808451203465679179)
    ·
      refine ⟨334831010712676805198518769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223220673808451203465679179 334831010712676805198518769)
      ·
        refine ⟨251123258034507603898889077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334831010712676805198518769 251123258034507603898889077)
        ·
          refine ⟨23542805440735087865520851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251123258034507603898889077 23542805440735087865520851)
          ·
            refine ⟨35314208161102631798281277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542805440735087865520851 35314208161102631798281277)
            ·
              refine ⟨13242828060413486924355479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35314208161102631798281277 13242828060413486924355479)
              ·
                refine ⟨19864242090620230386533219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13242828060413486924355479 19864242090620230386533219)
                ·
                  refine ⟨29796363135930345579799829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19864242090620230386533219 29796363135930345579799829)
                  ·
                    refine ⟨1396704521996734949053117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29796363135930345579799829 1396704521996734949053117)
                    ·
                      rfl

theorem cell23_8160217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_8160217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160217 prefixEnd_8160217 := by exact prefixLift 8160217
  have htrace : WordTrace (prefixWord ++ tailWord_8160217) baseStart_8160217 baseEnd_8160217 := by
    simpa [prefixWord, tailWord_8160217, baseEnd_8160217] using wordTrace_append hprefix tailTrace_8160217
  have hstable : (prefixWord ++ tailWord_8160217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160217).length < 2 ^ (prefixWord ++ tailWord_8160217).sum := by decide
  have hdescent : baseEnd_8160217 < baseStart_8160217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160308 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_8160308 : Nat := 118140960795 + 8160308 * 2 ^ 59
def prefixEnd_8160308 : Nat := 4983230072969 + 3 ^ 40 * 8160308 * 2
def baseEnd_8160308 : Nat := 4190160292729763991121433

theorem tailTrace_8160308 : CollatzResearch.WordTrace tailWord_8160308 prefixEnd_8160308 4190160292729763991121433 := by
  unfold tailWord_8160308
  simp only [CollatzResearch.WordTrace]
  refine ⟨148815442060302630247900789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198420589413736840330534385 148815442060302630247900789)
  ·
    refine ⟨13951447693153371585740699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148815442060302630247900789 13951447693153371585740699)
    ·
      refine ⟨20927171539730057378611049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13951447693153371585740699 20927171539730057378611049)
      ·
        refine ⟨15695378654797543033958287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20927171539730057378611049 15695378654797543033958287)
        ·
          refine ⟨23543067982196314550937431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15695378654797543033958287 23543067982196314550937431)
          ·
            refine ⟨35314601973294471826406147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23543067982196314550937431 35314601973294471826406147)
            ·
              refine ⟨52971902959941707739609221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35314601973294471826406147 52971902959941707739609221)
              ·
                refine ⟨9932231804989070201176729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52971902959941707739609221 9932231804989070201176729)
                ·
                  refine ⟨7449173853741802650882547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932231804989070201176729 7449173853741802650882547)
                  ·
                    refine ⟨11173760780612703976323821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449173853741802650882547 11173760780612703976323821)
                    ·
                      refine ⟨4190160292729763991121433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11173760780612703976323821 4190160292729763991121433)
                      ·
                        rfl

theorem cell23_8160308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_8160308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160308 prefixEnd_8160308 := by exact prefixLift 8160308
  have htrace : WordTrace (prefixWord ++ tailWord_8160308) baseStart_8160308 baseEnd_8160308 := by
    simpa [prefixWord, tailWord_8160308, baseEnd_8160308] using wordTrace_append hprefix tailTrace_8160308
  have hstable : (prefixWord ++ tailWord_8160308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160308).length < 2 ^ (prefixWord ++ tailWord_8160308).sum := by decide
  have hdescent : baseEnd_8160308 < baseStart_8160308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160327 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_8160327 : Nat := 118140960795 + 8160327 * 2 ^ 59
def prefixEnd_8160327 : Nat := 4983230072969 + 3 ^ 40 * 8160327 * 2
def baseEnd_8160327 : Nat := 4190170048862199416783845

theorem tailTrace_8160327 : CollatzResearch.WordTrace tailWord_8160327 prefixEnd_8160327 4190170048862199416783845 := by
  unfold tailWord_8160327
  simp only [CollatzResearch.WordTrace]
  refine ⟨297631577107536426740743235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198421051405024284493828823 297631577107536426740743235)
  ·
    refine ⟨446447365661304640111114853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297631577107536426740743235 446447365661304640111114853)
    ·
      refine ⟨83708881061494620020834035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446447365661304640111114853 83708881061494620020834035)
      ·
        refine ⟨125563321592241930031251053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83708881061494620020834035 125563321592241930031251053)
        ·
          refine ⟨47086245597090723761719145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125563321592241930031251053 47086245597090723761719145)
          ·
            refine ⟨35314684197818042821289359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47086245597090723761719145 35314684197818042821289359)
            ·
              refine ⟨52972026296727064231934039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35314684197818042821289359 52972026296727064231934039)
              ·
                refine ⟨79458039445090596347901059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52972026296727064231934039 79458039445090596347901059)
                ·
                  refine ⟨119187059167635894521851589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79458039445090596347901059 119187059167635894521851589)
                  ·
                    refine ⟨22347573593931730222847173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119187059167635894521851589 22347573593931730222847173)
                    ·
                      refine ⟨4190170048862199416783845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22347573593931730222847173 4190170048862199416783845)
                      ·
                        rfl

theorem cell23_8160327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_8160327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160327 prefixEnd_8160327 := by exact prefixLift 8160327
  have htrace : WordTrace (prefixWord ++ tailWord_8160327) baseStart_8160327 baseEnd_8160327 := by
    simpa [prefixWord, tailWord_8160327, baseEnd_8160327] using wordTrace_append hprefix tailTrace_8160327
  have hstable : (prefixWord ++ tailWord_8160327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160327).length < 2 ^ (prefixWord ++ tailWord_8160327).sum := by decide
  have hdescent : baseEnd_8160327 < baseStart_8160327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160365 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_8160365 : Nat := 118140960795 + 8160365 * 2 ^ 59
def prefixEnd_8160365 : Nat := 4983230072969 + 3 ^ 40 * 8160365 * 2
def baseEnd_8160365 : Nat := 4190189561127070268108671

theorem tailTrace_8160365 : CollatzResearch.WordTrace tailWord_8160365 prefixEnd_8160365 4190189561127070268108671 := by
  unfold tailWord_8160365
  simp only [CollatzResearch.WordTrace]
  refine ⟨297632963081398759230626549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198421975387599172820417699 297632963081398759230626549)
  ·
    refine ⟨27903090288881133677871239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297632963081398759230626549 27903090288881133677871239)
    ·
      refine ⟨41854635433321700516806859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27903090288881133677871239 41854635433321700516806859)
      ·
        refine ⟨62781953149982550775210289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41854635433321700516806859 62781953149982550775210289)
        ·
          refine ⟨47086464862486913081407717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62781953149982550775210289 47086464862486913081407717)
          ·
            refine ⟨8828712161716296202763947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47086464862486913081407717 8828712161716296202763947)
            ·
              refine ⟨13243068242574444304145921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828712161716296202763947 13243068242574444304145921)
              ·
                refine ⟨9932301181930833228109441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13243068242574444304145921 9932301181930833228109441)
                ·
                  refine ⟨7449225886448124921082081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932301181930833228109441 7449225886448124921082081)
                  ·
                    refine ⟨5586919414836093690811561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7449225886448124921082081 5586919414836093690811561)
                    ·
                      refine ⟨4190189561127070268108671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5586919414836093690811561 4190189561127070268108671)
                      ·
                        rfl

theorem cell23_8160365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_8160365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160365 prefixEnd_8160365 := by exact prefixLift 8160365
  have htrace : WordTrace (prefixWord ++ tailWord_8160365) baseStart_8160365 baseEnd_8160365 := by
    simpa [prefixWord, tailWord_8160365, baseEnd_8160365] using wordTrace_append hprefix tailTrace_8160365
  have hstable : (prefixWord ++ tailWord_8160365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160365).length < 2 ^ (prefixWord ++ tailWord_8160365).sum := by decide
  have hdescent : baseEnd_8160365 < baseStart_8160365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160367 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 4, 5]
def baseStart_8160367 : Nat := 118140960795 + 8160367 * 2 ^ 59
def prefixEnd_8160367 : Nat := 4983230072969 + 3 ^ 40 * 8160367 * 2
def baseEnd_8160367 : Nat := 1396730196029459753427887

theorem tailTrace_8160367 : CollatzResearch.WordTrace tailWord_8160367 prefixEnd_8160367 1396730196029459753427887 := by
  unfold tailWord_8160367
  simp only [CollatzResearch.WordTrace]
  refine ⟨297633036027391513572199355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198422024018261009048132903 297633036027391513572199355)
  ·
    refine ⟨446449554041087270358299033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297633036027391513572199355 446449554041087270358299033)
    ·
      refine ⟨334837165530815452768724275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446449554041087270358299033 334837165530815452768724275)
      ·
        refine ⟨502255748296223179153086413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334837165530815452768724275 502255748296223179153086413)
        ·
          refine ⟨188345905611083692182407405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502255748296223179153086413 188345905611083692182407405)
          ·
            refine ⟨70629714604156384568402777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188345905611083692182407405 70629714604156384568402777)
            ·
              refine ⟨52972285953117288426302083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70629714604156384568402777 52972285953117288426302083)
              ·
                refine ⟨79458428929675932639453125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52972285953117288426302083 79458428929675932639453125)
                ·
                  refine ⟨14898455424314237369897461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79458428929675932639453125 14898455424314237369897461)
                  ·
                    refine ⟨1396730196029459753427887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14898455424314237369897461 1396730196029459753427887)
                    ·
                      rfl

theorem cell23_8160367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_8160367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160367 prefixEnd_8160367 := by exact prefixLift 8160367
  have htrace : WordTrace (prefixWord ++ tailWord_8160367) baseStart_8160367 baseEnd_8160367 := by
    simpa [prefixWord, tailWord_8160367, baseEnd_8160367] using wordTrace_append hprefix tailTrace_8160367
  have hstable : (prefixWord ++ tailWord_8160367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160367).length < 2 ^ (prefixWord ++ tailWord_8160367).sum := by decide
  have hdescent : baseEnd_8160367 < baseStart_8160367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160387 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4]
def baseStart_8160387 : Nat := 118140960795 + 8160387 * 2 ^ 59
def prefixEnd_8160387 : Nat := 4983230072969 + 3 ^ 40 * 8160387 * 2
def baseEnd_8160387 : Nat := 4190200857701469182033569

theorem tailTrace_8160387 : CollatzResearch.WordTrace tailWord_8160387 prefixEnd_8160387 4190200857701469182033569 := by
  unfold tailWord_8160387
  simp only [CollatzResearch.WordTrace]
  refine ⟨297633765487319056987927415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198422510324879371325284943 297633765487319056987927415)
  ·
    refine ⟨446450648230978585481891123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297633765487319056987927415 446450648230978585481891123)
    ·
      refine ⟨669675972346467878222836685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446450648230978585481891123 669675972346467878222836685)
      ·
        refine ⟨251128489629925454333563757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 669675972346467878222836685 251128489629925454333563757)
        ·
          refine ⟨94173183611222045375086409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251128489629925454333563757 94173183611222045375086409)
          ·
            refine ⟨70629887708416534031314807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94173183611222045375086409 70629887708416534031314807)
            ·
              refine ⟨105944831562624801046972211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70629887708416534031314807 105944831562624801046972211)
              ·
                refine ⟨158917247343937201570458317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105944831562624801046972211 158917247343937201570458317)
                ·
                  refine ⟨59593967753976450588921869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158917247343937201570458317 59593967753976450588921869)
                  ·
                    refine ⟨22347737907741168970845701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59593967753976450588921869 22347737907741168970845701)
                    ·
                      refine ⟨4190200857701469182033569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22347737907741168970845701 4190200857701469182033569)
                      ·
                        rfl

theorem cell23_8160387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_8160387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160387 prefixEnd_8160387 := by exact prefixLift 8160387
  have htrace : WordTrace (prefixWord ++ tailWord_8160387) baseStart_8160387 baseEnd_8160387 := by
    simpa [prefixWord, tailWord_8160387, baseEnd_8160387] using wordTrace_append hprefix tailTrace_8160387
  have hstable : (prefixWord ++ tailWord_8160387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160387).length < 2 ^ (prefixWord ++ tailWord_8160387).sum := by decide
  have hdescent : baseEnd_8160387 < baseStart_8160387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160431 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 1, 4]
def baseStart_8160431 : Nat := 118140960795 + 8160431 * 2 ^ 59
def prefixEnd_8160431 : Nat := 4983230072969 + 3 ^ 40 * 8160431 * 2
def baseEnd_8160431 : Nat := 1396741150283422336627789

theorem tailTrace_8160431 : CollatzResearch.WordTrace tailWord_8160431 prefixEnd_8160431 1396741150283422336627789 := by
  unfold tailWord_8160431
  simp only [CollatzResearch.WordTrace]
  refine ⟨297635370299159652502529147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198423580199439768335019431 297635370299159652502529147)
  ·
    refine ⟨446453055448739478753793721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297635370299159652502529147 446453055448739478753793721)
    ·
      refine ⟨334839791586554609065345291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446453055448739478753793721 334839791586554609065345291)
      ·
        refine ⟨502259687379831913598017937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334839791586554609065345291 502259687379831913598017937)
        ·
          refine ⟨376694765534873935198513453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502259687379831913598017937 376694765534873935198513453)
          ·
            refine ⟨141260537075577725699442545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376694765534873935198513453 141260537075577725699442545)
            ·
              refine ⟨105945402806683294274581909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141260537075577725699442545 105945402806683294274581909)
              ·
                refine ⟨4966190756563279419121027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105945402806683294274581909 4966190756563279419121027)
                ·
                  refine ⟨7449286134844919128681541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966190756563279419121027 7449286134844919128681541)
                  ·
                    refine ⟨1396741150283422336627789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449286134844919128681541 1396741150283422336627789)
                    ·
                      rfl

theorem cell23_8160431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 4].length) (baseStart_8160431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160431 prefixEnd_8160431 := by exact prefixLift 8160431
  have htrace : WordTrace (prefixWord ++ tailWord_8160431) baseStart_8160431 baseEnd_8160431 := by
    simpa [prefixWord, tailWord_8160431, baseEnd_8160431] using wordTrace_append hprefix tailTrace_8160431
  have hstable : (prefixWord ++ tailWord_8160431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160431).length < 2 ^ (prefixWord ++ tailWord_8160431).sum := by decide
  have hdescent : baseEnd_8160431 < baseStart_8160431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160447 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_8160447 : Nat := 118140960795 + 8160447 * 2 ^ 59
def prefixEnd_8160447 : Nat := 4983230072969 + 3 ^ 40 * 8160447 * 2
def baseEnd_8160447 : Nat := 4190231666540738947283293

theorem tailTrace_8160447 : CollatzResearch.WordTrace tailWord_8160447 prefixEnd_8160447 4190231666540738947283293 := by
  unfold tailWord_8160447
  simp only [CollatzResearch.WordTrace]
  refine ⟨297635953867101687235111595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198423969244734458156741063 297635953867101687235111595)
  ·
    refine ⟨446453930800652530852667393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297635953867101687235111595 446453930800652530852667393)
    ·
      refine ⟨334840448100489398139500545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446453930800652530852667393 334840448100489398139500545)
      ·
        refine ⟨251130336075367048604625409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334840448100489398139500545 251130336075367048604625409)
        ·
          refine ⟨188347752056525286453469057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251130336075367048604625409 188347752056525286453469057)
          ·
            refine ⟨141260814042393964840101793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188347752056525286453469057 141260814042393964840101793)
            ·
              refine ⟨105945610531795473630076345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141260814042393964840101793 105945610531795473630076345)
              ·
                refine ⟨79459207898846605222557259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105945610531795473630076345 79459207898846605222557259)
                ·
                  refine ⟨119188811848269907833835889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79459207898846605222557259 119188811848269907833835889)
                  ·
                    refine ⟨89391608886202430875376917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119188811848269907833835889 89391608886202430875376917)
                    ·
                      refine ⟨4190231666540738947283293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89391608886202430875376917 4190231666540738947283293)
                      ·
                        rfl

theorem cell23_8160447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_8160447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160447 prefixEnd_8160447 := by exact prefixLift 8160447
  have htrace : WordTrace (prefixWord ++ tailWord_8160447) baseStart_8160447 baseEnd_8160447 := by
    simpa [prefixWord, tailWord_8160447, baseEnd_8160447] using wordTrace_append hprefix tailTrace_8160447
  have hstable : (prefixWord ++ tailWord_8160447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160447).length < 2 ^ (prefixWord ++ tailWord_8160447).sum := by decide
  have hdescent : baseEnd_8160447 < baseStart_8160447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160504 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 8, 4]
def baseStart_8160504 : Nat := 118140960795 + 8160504 * 2 ^ 59
def prefixEnd_8160504 : Nat := 4983230072969 + 3 ^ 40 * 8160504 * 2
def baseEnd_8160504 : Nat := 1396753644979348408090177

theorem tailTrace_8160504 : CollatzResearch.WordTrace tailWord_8160504 prefixEnd_8160504 1396753644979348408090177 := by
  unfold tailWord_8160504
  simp only [CollatzResearch.WordTrace]
  refine ⟨148819016413947592984968283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198425355218596790646624377 148819016413947592984968283)
  ·
    refine ⟨223228524620921389477452425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148819016413947592984968283 223228524620921389477452425)
    ·
      refine ⟨167421393465691042108089319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223228524620921389477452425 167421393465691042108089319)
      ·
        refine ⟨251132090198536563162133979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167421393465691042108089319 251132090198536563162133979)
        ·
          refine ⟨376698135297804844743200969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251132090198536563162133979 376698135297804844743200969)
          ·
            refine ⟨282523601473353633557400727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376698135297804844743200969 282523601473353633557400727)
            ·
              refine ⟨423785402210030450336101091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282523601473353633557400727 423785402210030450336101091)
              ·
                refine ⟨635678103315045675504151637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423785402210030450336101091 635678103315045675504151637)
                ·
                  refine ⟨7449352773223191509814277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 635678103315045675504151637 7449352773223191509814277)
                  ·
                    refine ⟨1396753644979348408090177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449352773223191509814277 1396753644979348408090177)
                    ·
                      rfl

theorem cell23_8160504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_8160504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160504 prefixEnd_8160504 := by exact prefixLift 8160504
  have htrace : WordTrace (prefixWord ++ tailWord_8160504) baseStart_8160504 baseEnd_8160504 := by
    simpa [prefixWord, tailWord_8160504, baseEnd_8160504] using wordTrace_append hprefix tailTrace_8160504
  have hstable : (prefixWord ++ tailWord_8160504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160504).length < 2 ^ (prefixWord ++ tailWord_8160504).sum := by decide
  have hdescent : baseEnd_8160504 < baseStart_8160504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160538 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_8160538 : Nat := 118140960795 + 8160538 * 2 ^ 59
def prefixEnd_8160538 : Nat := 4983230072969 + 3 ^ 40 * 8160538 * 2
def baseEnd_8160538 : Nat := 1396759464426766030415125

theorem tailTrace_8160538 : CollatzResearch.WordTrace tailWord_8160538 prefixEnd_8160538 1396759464426766030415125 := by
  unfold tailWord_8160538
  simp only [CollatzResearch.WordTrace]
  refine ⟨74409818227443002444168567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198426181939848006517782845 74409818227443002444168567)
  ·
    refine ⟨111614727341164503666252851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74409818227443002444168567 111614727341164503666252851)
    ·
      refine ⟨167422091011746755499379277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111614727341164503666252851 167422091011746755499379277)
      ·
        refine ⟨62783284129405033312267229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167422091011746755499379277 62783284129405033312267229)
        ·
          refine ⟨23543731548526887492100211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62783284129405033312267229 23543731548526887492100211)
          ·
            refine ⟨35315597322790331238150317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23543731548526887492100211 35315597322790331238150317)
            ·
              refine ⟨13243348996046374214306369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35315597322790331238150317 13243348996046374214306369)
              ·
                refine ⟨9932511747034780660729777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13243348996046374214306369 9932511747034780660729777)
                ·
                  refine ⟨7449383810276085495547333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932511747034780660729777 7449383810276085495547333)
                  ·
                    refine ⟨1396759464426766030415125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449383810276085495547333 1396759464426766030415125)
                    ·
                      rfl

theorem cell23_8160538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_8160538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160538 prefixEnd_8160538 := by exact prefixLift 8160538
  have htrace : WordTrace (prefixWord ++ tailWord_8160538) baseStart_8160538 baseEnd_8160538 := by
    simpa [prefixWord, tailWord_8160538, baseEnd_8160538] using wordTrace_append hprefix tailTrace_8160538
  have hstable : (prefixWord ++ tailWord_8160538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160538).length < 2 ^ (prefixWord ++ tailWord_8160538).sum := by decide
  have hdescent : baseEnd_8160538 < baseStart_8160538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160571 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 9, 3, 2]
def baseStart_8160571 : Nat := 118140960795 + 8160571 * 2 ^ 59
def prefixEnd_8160571 : Nat := 4983230072969 + 3 ^ 40 * 8160571 * 2
def baseEnd_8160571 : Nat := 4190295338141896462132723

theorem tailTrace_8160571 : CollatzResearch.WordTrace tailWord_8160571 prefixEnd_8160571 4190295338141896462132723 := by
  unfold tailWord_8160571
  simp only [CollatzResearch.WordTrace]
  refine ⟨297640476518652456412625567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198426984345768304275083711 297640476518652456412625567)
  ·
    refine ⟨446460714777978684618938351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297640476518652456412625567 446460714777978684618938351)
    ·
      refine ⟨669691072166968026928407527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446460714777978684618938351 669691072166968026928407527)
      ·
        refine ⟨1004536608250452040392611291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669691072166968026928407527 1004536608250452040392611291)
        ·
          refine ⟨1506804912375678060588916937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004536608250452040392611291 1506804912375678060588916937)
          ·
            refine ⟨1130103684281758545441687703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506804912375678060588916937 1130103684281758545441687703)
            ·
              refine ⟨1695155526422637818162531555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130103684281758545441687703 1695155526422637818162531555)
              ·
                refine ⟨2542733289633956727243797333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695155526422637818162531555 2542733289633956727243797333)
                ·
                  refine ⟨14898827868948965198694125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2542733289633956727243797333 14898827868948965198694125)
                  ·
                    refine ⟨5587060450855861949510297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14898827868948965198694125 5587060450855861949510297)
                    ·
                      refine ⟨4190295338141896462132723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587060450855861949510297 4190295338141896462132723)
                      ·
                        rfl

theorem cell23_8160571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3, 2].length) (baseStart_8160571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160571 prefixEnd_8160571 := by exact prefixLift 8160571
  have htrace : WordTrace (prefixWord ++ tailWord_8160571) baseStart_8160571 baseEnd_8160571 := by
    simpa [prefixWord, tailWord_8160571, baseEnd_8160571] using wordTrace_append hprefix tailTrace_8160571
  have hstable : (prefixWord ++ tailWord_8160571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160571).length < 2 ^ (prefixWord ++ tailWord_8160571).sum := by decide
  have hdescent : baseEnd_8160571 < baseStart_8160571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160582 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_8160582 : Nat := 118140960795 + 8160582 * 2 ^ 59
def prefixEnd_8160582 : Nat := 4983230072969 + 3 ^ 40 * 8160582 * 2
def baseEnd_8160582 : Nat := 4190300986429095919095173

theorem tailTrace_8160582 : CollatzResearch.WordTrace tailWord_8160582 prefixEnd_8160582 4190300986429095919095173 := by
  unfold tailWord_8160582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301277428800393915352375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198427251814408403527517333 9301277428800393915352375)
  ·
    refine ⟨13951916143200590873028563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9301277428800393915352375 13951916143200590873028563)
    ·
      refine ⟨20927874214800886309542845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13951916143200590873028563 20927874214800886309542845)
      ·
        refine ⟨7847952830550332366078567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20927874214800886309542845 7847952830550332366078567)
        ·
          refine ⟨11771929245825498549117851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847952830550332366078567 11771929245825498549117851)
          ·
            refine ⟨17657893868738247823676777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771929245825498549117851 17657893868738247823676777)
            ·
              refine ⟨13243420401553685867757583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17657893868738247823676777 13243420401553685867757583)
              ·
                refine ⟨19865130602330528801636375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13243420401553685867757583 19865130602330528801636375)
                ·
                  refine ⟨29797695903495793202454563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19865130602330528801636375 29797695903495793202454563)
                  ·
                    refine ⟨44696543855243689803681845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29797695903495793202454563 44696543855243689803681845)
                    ·
                      refine ⟨4190300986429095919095173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44696543855243689803681845 4190300986429095919095173)
                      ·
                        rfl

theorem cell23_8160582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_8160582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160582 prefixEnd_8160582 := by exact prefixLift 8160582
  have htrace : WordTrace (prefixWord ++ tailWord_8160582) baseStart_8160582 baseEnd_8160582 := by
    simpa [prefixWord, tailWord_8160582, baseEnd_8160582] using wordTrace_append hprefix tailTrace_8160582
  have hstable : (prefixWord ++ tailWord_8160582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160582).length < 2 ^ (prefixWord ++ tailWord_8160582).sum := by decide
  have hdescent : baseEnd_8160582 < baseStart_8160582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160584 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_8160584 : Nat := 118140960795 + 8160584 * 2 ^ 59
def prefixEnd_8160584 : Nat := 4983230072969 + 3 ^ 40 * 8160584 * 2
def baseEnd_8160584 : Nat := 4190302013390404911270163

theorem tailTrace_8160584 : CollatzResearch.WordTrace tailWord_8160584 prefixEnd_8160584 4190302013390404911270163 := by
  unfold tailWord_8160584
  simp only [CollatzResearch.WordTrace]
  refine ⟨148820475333802679816424403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198427300445070239755232537 148820475333802679816424403)
  ·
    refine ⟨223230713000704019724636605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148820475333802679816424403 223230713000704019724636605)
    ·
      refine ⟨83711517375264007396738727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223230713000704019724636605 83711517375264007396738727)
      ·
        refine ⟨125567276062896011095108091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83711517375264007396738727 125567276062896011095108091)
        ·
          refine ⟨188350914094344016642662137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125567276062896011095108091 188350914094344016642662137)
          ·
            refine ⟨141263185570758012481996603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188350914094344016642662137 141263185570758012481996603)
            ·
              refine ⟨211894778356137018722994905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141263185570758012481996603 211894778356137018722994905)
              ·
                refine ⟨158921083767102764042246179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211894778356137018722994905 158921083767102764042246179)
                ·
                  refine ⟨238381625650654146063369269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158921083767102764042246179 238381625650654146063369269)
                  ·
                    refine ⟨22348277404748826193440869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 238381625650654146063369269 22348277404748826193440869)
                    ·
                      refine ⟨4190302013390404911270163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22348277404748826193440869 4190302013390404911270163)
                      ·
                        rfl

theorem cell23_8160584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_8160584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160584 prefixEnd_8160584 := by exact prefixLift 8160584
  have htrace : WordTrace (prefixWord ++ tailWord_8160584) baseStart_8160584 baseEnd_8160584 := by
    simpa [prefixWord, tailWord_8160584, baseEnd_8160584] using wordTrace_append hprefix tailTrace_8160584
  have hstable : (prefixWord ++ tailWord_8160584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160584).length < 2 ^ (prefixWord ++ tailWord_8160584).sum := by decide
  have hdescent : baseEnd_8160584 < baseStart_8160584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160612 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_8160612 : Nat := 118140960795 + 8160612 * 2 ^ 59
def prefixEnd_8160612 : Nat := 4983230072969 + 3 ^ 40 * 8160612 * 2
def baseEnd_8160612 : Nat := 4190316390848730801720035

theorem tailTrace_8160612 : CollatzResearch.WordTrace tailWord_8160612 prefixEnd_8160612 4190316390848730801720035 := by
  unfold tailWord_8160612
  simp only [CollatzResearch.WordTrace]
  refine ⟨148820985955751960207434045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198427981274335946943245393 148820985955751960207434045)
  ·
    refine ⟨55807869733406985077787767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148820985955751960207434045 55807869733406985077787767)
    ·
      refine ⟨83711804600110477616681651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55807869733406985077787767 83711804600110477616681651)
      ·
        refine ⟨125567706900165716425022477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83711804600110477616681651 125567706900165716425022477)
        ·
          refine ⟨47087890087562143659383429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125567706900165716425022477 47087890087562143659383429)
          ·
            refine ⟨8828979391417901936134393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47087890087562143659383429 8828979391417901936134393)
            ·
              refine ⟨6621734543563426452100795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8828979391417901936134393 6621734543563426452100795)
              ·
                refine ⟨9932601815345139678151193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621734543563426452100795 9932601815345139678151193)
                ·
                  refine ⟨7449451361508854758613395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932601815345139678151193 7449451361508854758613395)
                  ·
                    refine ⟨11174177042263282137920093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449451361508854758613395 11174177042263282137920093)
                    ·
                      refine ⟨4190316390848730801720035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174177042263282137920093 4190316390848730801720035)
                      ·
                        rfl

theorem cell23_8160612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_8160612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160612 prefixEnd_8160612 := by exact prefixLift 8160612
  have htrace : WordTrace (prefixWord ++ tailWord_8160612) baseStart_8160612 baseEnd_8160612 := by
    simpa [prefixWord, tailWord_8160612, baseEnd_8160612] using wordTrace_append hprefix tailTrace_8160612
  have hstable : (prefixWord ++ tailWord_8160612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160612).length < 2 ^ (prefixWord ++ tailWord_8160612).sum := by decide
  have hdescent : baseEnd_8160612 < baseStart_8160612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160621 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_8160621 : Nat := 118140960795 + 8160621 * 2 ^ 59
def prefixEnd_8160621 : Nat := 4983230072969 + 3 ^ 40 * 8160621 * 2
def baseEnd_8160621 : Nat := 4190321012174621266507493

theorem tailTrace_8160621 : CollatzResearch.WordTrace tailWord_8160621 prefixEnd_8160621 4190321012174621266507493 := by
  unfold tailWord_8160621
  simp only [CollatzResearch.WordTrace]
  refine ⟨297642300168471314951945717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198428200112314209967963811 297642300168471314951945717)
  ·
    refine ⟨27903965640794185776744911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297642300168471314951945717 27903965640794185776744911)
    ·
      refine ⟨41855948461191278665117367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27903965640794185776744911 41855948461191278665117367)
      ·
        refine ⟨62783922691786917997676051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41855948461191278665117367 62783922691786917997676051)
        ·
          refine ⟨94175884037680376996514077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62783922691786917997676051 94175884037680376996514077)
          ·
            refine ⟨35315956514130141373692779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94175884037680376996514077 35315956514130141373692779)
            ·
              refine ⟨52973934771195212060539169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35315956514130141373692779 52973934771195212060539169)
              ·
                refine ⟨39730451078396409045404377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52973934771195212060539169 39730451078396409045404377)
                ·
                  refine ⟨29797838308797306784053283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39730451078396409045404377 29797838308797306784053283)
                  ·
                    refine ⟨44696757463195960176079925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29797838308797306784053283 44696757463195960176079925)
                    ·
                      refine ⟨4190321012174621266507493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44696757463195960176079925 4190321012174621266507493)
                      ·
                        rfl

theorem cell23_8160621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_8160621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160621 prefixEnd_8160621 := by exact prefixLift 8160621
  have htrace : WordTrace (prefixWord ++ tailWord_8160621) baseStart_8160621 baseEnd_8160621 := by
    simpa [prefixWord, tailWord_8160621, baseEnd_8160621] using wordTrace_append hprefix tailTrace_8160621
  have hstable : (prefixWord ++ tailWord_8160621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160621).length < 2 ^ (prefixWord ++ tailWord_8160621).sum := by decide
  have hdescent : baseEnd_8160621 < baseStart_8160621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160622 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_8160622 : Nat := 118140960795 + 8160622 * 2 ^ 59
def prefixEnd_8160622 : Nat := 4983230072969 + 3 ^ 40 * 8160622 * 2
def baseEnd_8160622 : Nat := 4190321525655275762594989

theorem tailTrace_8160622 : CollatzResearch.WordTrace tailWord_8160622 prefixEnd_8160622 4190321525655275762594989 := by
  unfold tailWord_8160622
  simp only [CollatzResearch.WordTrace]
  refine ⟨37205292080183461515341515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198428224427645128081821413 37205292080183461515341515)
  ·
    refine ⟨55807938120275192273012273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37205292080183461515341515 55807938120275192273012273)
    ·
      refine ⟨41855953590206394204759205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55807938120275192273012273 41855953590206394204759205)
      ·
        refine ⟨7847991298163698913392351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41855953590206394204759205 7847991298163698913392351)
        ·
          refine ⟨11771986947245548370088527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847991298163698913392351 11771986947245548370088527)
          ·
            refine ⟨17657980420868322555132791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771986947245548370088527 17657980420868322555132791)
            ·
              refine ⟨26486970631302483832699187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17657980420868322555132791 26486970631302483832699187)
              ·
                refine ⟨39730455946953725749048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26486970631302483832699187 39730455946953725749048781)
                ·
                  refine ⟨14898920980107647155893293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39730455946953725749048781 14898920980107647155893293)
                  ·
                    refine ⟨5587095367540367683459985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14898920980107647155893293 5587095367540367683459985)
                    ·
                      refine ⟨4190321525655275762594989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587095367540367683459985 4190321525655275762594989)
                      ·
                        rfl

theorem cell23_8160622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_8160622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160622 prefixEnd_8160622 := by exact prefixLift 8160622
  have htrace : WordTrace (prefixWord ++ tailWord_8160622) baseStart_8160622 baseEnd_8160622 := by
    simpa [prefixWord, tailWord_8160622, baseEnd_8160622] using wordTrace_append hprefix tailTrace_8160622
  have hstable : (prefixWord ++ tailWord_8160622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160622).length < 2 ^ (prefixWord ++ tailWord_8160622).sum := by decide
  have hdescent : baseEnd_8160622 < baseStart_8160622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160624 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 9]
def baseStart_8160624 : Nat := 118140960795 + 8160624 * 2 ^ 59
def prefixEnd_8160624 : Nat := 4983230072969 + 3 ^ 40 * 8160624 * 2
def baseEnd_8160624 : Nat := 465591394735176083863331

theorem tailTrace_8160624 : CollatzResearch.WordTrace tailWord_8160624 prefixEnd_8160624 465591394735176083863331 := by
  unfold tailWord_8160624
  simp only [CollatzResearch.WordTrace]
  refine ⟨148821204793730223232152463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198428273058306964309536617 148821204793730223232152463)
  ·
    refine ⟨223231807190595334848228695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148821204793730223232152463 223231807190595334848228695)
    ·
      refine ⟨334847710785893002272343043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223231807190595334848228695 334847710785893002272343043)
      ·
        refine ⟨502271566178839503408514565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334847710785893002272343043 502271566178839503408514565)
        ·
          refine ⟨94175918658532406889096481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 502271566178839503408514565 94175918658532406889096481)
          ·
            refine ⟨70631938993899305166822361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94175918658532406889096481 70631938993899305166822361)
            ·
              refine ⟨52973954245424478875116771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70631938993899305166822361 52973954245424478875116771)
              ·
                refine ⟨79460931368136718312675157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52973954245424478875116771 79460931368136718312675157)
                ·
                  refine ⟨465591394735176083863331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79460931368136718312675157 465591394735176083863331)
                  ·
                    rfl

theorem cell23_8160624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_8160624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160624 prefixEnd_8160624 := by exact prefixLift 8160624
  have htrace : WordTrace (prefixWord ++ tailWord_8160624) baseStart_8160624 baseEnd_8160624 := by
    simpa [prefixWord, tailWord_8160624, baseEnd_8160624] using wordTrace_append hprefix tailTrace_8160624
  have hstable : (prefixWord ++ tailWord_8160624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160624).length < 2 ^ (prefixWord ++ tailWord_8160624).sum := by decide
  have hdescent : baseEnd_8160624 < baseStart_8160624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160651 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 3]
def baseStart_8160651 : Nat := 118140960795 + 8160651 * 2 ^ 59
def prefixEnd_8160651 : Nat := 4983230072969 + 3 ^ 40 * 8160651 * 2
def baseEnd_8160651 : Nat := 4190336416594256149132355

theorem tailTrace_8160651 : CollatzResearch.WordTrace tailWord_8160651 prefixEnd_8160651 4190336416594256149132355 := by
  unfold tailWord_8160651
  simp only [CollatzResearch.WordTrace]
  refine ⟨297643394358362630075537807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198428929572241753383691871 297643394358362630075537807)
  ·
    refine ⟨446465091537543945113306711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297643394358362630075537807 446465091537543945113306711)
    ·
      refine ⟨669697637306315917669960067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446465091537543945113306711 669697637306315917669960067)
      ·
        refine ⟨1004546455959473876504940101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669697637306315917669960067 1004546455959473876504940101)
        ·
          refine ⟨188352460492401351844676269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1004546455959473876504940101 188352460492401351844676269)
          ·
            refine ⟨70632172684650506941753601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188352460492401351844676269 70632172684650506941753601)
            ·
              refine ⟨52974129513487880206315201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70632172684650506941753601 52974129513487880206315201)
              ·
                refine ⟨39730597135115910154736401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52974129513487880206315201 39730597135115910154736401)
                ·
                  refine ⟨29797947851336932616052301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39730597135115910154736401 29797947851336932616052301)
                  ·
                    refine ⟨11174230444251349731019613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29797947851336932616052301 11174230444251349731019613)
                    ·
                      refine ⟨4190336416594256149132355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174230444251349731019613 4190336416594256149132355)
                      ·
                        rfl

theorem cell23_8160651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 3].length) (baseStart_8160651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160651 prefixEnd_8160651 := by exact prefixLift 8160651
  have htrace : WordTrace (prefixWord ++ tailWord_8160651) baseStart_8160651 baseEnd_8160651 := by
    simpa [prefixWord, tailWord_8160651, baseEnd_8160651] using wordTrace_append hprefix tailTrace_8160651
  have hstable : (prefixWord ++ tailWord_8160651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160651).length < 2 ^ (prefixWord ++ tailWord_8160651).sum := by decide
  have hdescent : baseEnd_8160651 < baseStart_8160651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160718 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_8160718 : Nat := 118140960795 + 8160718 * 2 ^ 59
def prefixEnd_8160718 : Nat := 4983230072969 + 3 ^ 40 * 8160718 * 2
def baseEnd_8160718 : Nat := 1396790273266035795664849

theorem tailTrace_8160718 : CollatzResearch.WordTrace tailWord_8160718 prefixEnd_8160718 1396790273266035795664849 := by
  unfold tailWord_8160718
  simp only [CollatzResearch.WordTrace]
  refine ⟨37205729756139987564778351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198430558699413267012151205 37205729756139987564778351)
  ·
    refine ⟨55808594634209981347167527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37205729756139987564778351 55808594634209981347167527)
    ·
      refine ⟨83712891951314972020751291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55808594634209981347167527 83712891951314972020751291)
      ·
        refine ⟨125569337926972458031126937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83712891951314972020751291 125569337926972458031126937)
        ·
          refine ⟨94177003445229343523345203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125569337926972458031126937 94177003445229343523345203)
          ·
            refine ⟨141265505167844015285017805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94177003445229343523345203 141265505167844015285017805)
            ·
              refine ⟨52974564437941505731881677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141265505167844015285017805 52974564437941505731881677)
              ·
                refine ⟨19865461664228064649455629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52974564437941505731881677 19865461664228064649455629)
                ·
                  refine ⟨7449548124085524243545861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19865461664228064649455629 7449548124085524243545861)
                  ·
                    refine ⟨1396790273266035795664849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449548124085524243545861 1396790273266035795664849)
                    ·
                      rfl

theorem cell23_8160718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_8160718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160718 prefixEnd_8160718 := by exact prefixLift 8160718
  have htrace : WordTrace (prefixWord ++ tailWord_8160718) baseStart_8160718 baseEnd_8160718 := by
    simpa [prefixWord, tailWord_8160718, baseEnd_8160718] using wordTrace_append hprefix tailTrace_8160718
  have hstable : (prefixWord ++ tailWord_8160718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160718).length < 2 ^ (prefixWord ++ tailWord_8160718).sum := by decide
  have hdescent : baseEnd_8160718 < baseStart_8160718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160752 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 1, 4]
def baseStart_8160752 : Nat := 118140960795 + 8160752 * 2 ^ 59
def prefixEnd_8160752 : Nat := 4983230072969 + 3 ^ 40 * 8160752 * 2
def baseEnd_8160752 : Nat := 1396796092713453417989797

theorem tailTrace_8160752 : CollatzResearch.WordTrace tailWord_8160752 prefixEnd_8160752 1396796092713453417989797 := by
  unfold tailWord_8160752
  simp only [CollatzResearch.WordTrace]
  refine ⟨148823539065498362162482255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198431385420664482883309673 148823539065498362162482255)
  ·
    refine ⟨223235308598247543243723383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148823539065498362162482255 223235308598247543243723383)
    ·
      refine ⟨334852962897371314865585075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223235308598247543243723383 334852962897371314865585075)
      ·
        refine ⟨502279444346056972298377613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334852962897371314865585075 502279444346056972298377613)
        ·
          refine ⟨188354791629771364611891605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502279444346056972298377613 188354791629771364611891605)
          ·
            refine ⟨8829130857645532716182419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188354791629771364611891605 8829130857645532716182419)
            ·
              refine ⟨13243696286468299074273629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8829130857645532716182419 13243696286468299074273629)
              ·
                refine ⟨4966386107425612152852611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13243696286468299074273629 4966386107425612152852611)
                ·
                  refine ⟨7449579161138418229278917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966386107425612152852611 7449579161138418229278917)
                  ·
                    refine ⟨1396796092713453417989797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449579161138418229278917 1396796092713453417989797)
                    ·
                      rfl

theorem cell23_8160752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 4].length) (baseStart_8160752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160752 prefixEnd_8160752 := by exact prefixLift 8160752
  have htrace : WordTrace (prefixWord ++ tailWord_8160752) baseStart_8160752 baseEnd_8160752 := by
    simpa [prefixWord, tailWord_8160752, baseEnd_8160752] using wordTrace_append hprefix tailTrace_8160752
  have hstable : (prefixWord ++ tailWord_8160752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160752).length < 2 ^ (prefixWord ++ tailWord_8160752).sum := by decide
  have hdescent : baseEnd_8160752 < baseStart_8160752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160761 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_8160761 : Nat := 118140960795 + 8160761 * 2 ^ 59
def prefixEnd_8160761 : Nat := 4983230072969 + 3 ^ 40 * 8160761 * 2
def baseEnd_8160761 : Nat := 1396797633155416906252283

theorem tailTrace_8160761 : CollatzResearch.WordTrace tailWord_8160761 prefixEnd_8160761 1396797633155416906252283 := by
  unfold tailWord_8160761
  simp only [CollatzResearch.WordTrace]
  refine ⟨297647406387964118862042137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198431604258642745908028091 297647406387964118862042137)
  ·
    refine ⟨223235554790973089146531603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297647406387964118862042137 223235554790973089146531603)
    ·
      refine ⟨334853332186459633719797405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223235554790973089146531603 334853332186459633719797405)
      ·
        refine ⟨125569999569922362644924027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334853332186459633719797405 125569999569922362644924027)
        ·
          refine ⟨188354999354883543967386041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125569999569922362644924027 188354999354883543967386041)
          ·
            refine ⟨141266249516162657975539531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188354999354883543967386041 141266249516162657975539531)
            ·
              refine ⟨211899374274243986963309297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141266249516162657975539531 211899374274243986963309297)
              ·
                refine ⟨158924530705682990222481973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211899374274243986963309297 158924530705682990222481973)
                ·
                  refine ⟨14899174753657780333357685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158924530705682990222481973 14899174753657780333357685)
                  ·
                    refine ⟨1396797633155416906252283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14899174753657780333357685 1396797633155416906252283)
                    ·
                      rfl

theorem cell23_8160761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_8160761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160761 prefixEnd_8160761 := by exact prefixLift 8160761
  have htrace : WordTrace (prefixWord ++ tailWord_8160761) baseStart_8160761 baseEnd_8160761 := by
    simpa [prefixWord, tailWord_8160761, baseEnd_8160761] using wordTrace_append hprefix tailTrace_8160761
  have hstable : (prefixWord ++ tailWord_8160761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160761).length < 2 ^ (prefixWord ++ tailWord_8160761).sum := by decide
  have hdescent : baseEnd_8160761 < baseStart_8160761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160769 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 1, 4]
def baseStart_8160769 : Nat := 118140960795 + 8160769 * 2 ^ 59
def prefixEnd_8160769 : Nat := 4983230072969 + 3 ^ 40 * 8160769 * 2
def baseEnd_8160769 : Nat := 1396799002437162229152271

theorem tailTrace_8160769 : CollatzResearch.WordTrace tailWord_8160769 prefixEnd_8160769 1396799002437162229152271 := by
  unfold tailWord_8160769
  simp only [CollatzResearch.WordTrace]
  refine ⟨297647698171935136228333361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198431798781290090818888907 297647698171935136228333361)
  ·
    refine ⟨223235773628951352171250021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297647698171935136228333361 223235773628951352171250021)
    ·
      refine ⟨41856707555428378532109379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223235773628951352171250021 41856707555428378532109379)
      ·
        refine ⟨62785061333142567798164069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41856707555428378532109379 62785061333142567798164069)
        ·
          refine ⟨11772198999964231462155763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62785061333142567798164069 11772198999964231462155763)
          ·
            refine ⟨17658298499946347193233645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772198999964231462155763 17658298499946347193233645)
            ·
              refine ⟨6621861937479880197462617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17658298499946347193233645 6621861937479880197462617)
              ·
                refine ⟨4966396453109910148096963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621861937479880197462617 4966396453109910148096963)
                ·
                  refine ⟨7449594679664865222145445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966396453109910148096963 7449594679664865222145445)
                  ·
                    refine ⟨1396799002437162229152271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449594679664865222145445 1396799002437162229152271)
                    ·
                      rfl

theorem cell23_8160769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_8160769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160769 prefixEnd_8160769 := by exact prefixLift 8160769
  have htrace : WordTrace (prefixWord ++ tailWord_8160769) baseStart_8160769 baseEnd_8160769 := by
    simpa [prefixWord, tailWord_8160769, baseEnd_8160769] using wordTrace_append hprefix tailTrace_8160769
  have hstable : (prefixWord ++ tailWord_8160769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160769).length < 2 ^ (prefixWord ++ tailWord_8160769).sum := by decide
  have hdescent : baseEnd_8160769 < baseStart_8160769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160782 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_8160782 : Nat := 118140960795 + 8160782 * 2 ^ 59
def prefixEnd_8160782 : Nat := 4983230072969 + 3 ^ 40 * 8160782 * 2
def baseEnd_8160782 : Nat := 465600409173332792954917

theorem tailTrace_8160782 : CollatzResearch.WordTrace tailWord_8160782 prefixEnd_8160782 465600409173332792954917 := by
  unfold tailWord_8160782
  simp only [CollatzResearch.WordTrace]
  refine ⟨37206021540111004931069575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198432114880592026299037733 37206021540111004931069575)
  ·
    refine ⟨55809032310166507396604363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37206021540111004931069575 55809032310166507396604363)
    ·
      refine ⟨83713548465249761094906545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55809032310166507396604363 83713548465249761094906545)
      ·
        refine ⟨62785161348937320821179909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83713548465249761094906545 62785161348937320821179909)
        ·
          refine ⟨11772217752925747653971233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62785161348937320821179909 11772217752925747653971233)
          ·
            refine ⟨8829163314694310740478425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11772217752925747653971233 8829163314694310740478425)
            ·
              refine ⟨6621872486020733055358819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829163314694310740478425 6621872486020733055358819)
              ·
                refine ⟨9932808729031099583038229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621872486020733055358819 9932808729031099583038229)
                ·
                  refine ⟨465600409173332792954917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9932808729031099583038229 465600409173332792954917)
                  ·
                    rfl

theorem cell23_8160782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_8160782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160782 prefixEnd_8160782 := by exact prefixLift 8160782
  have htrace : WordTrace (prefixWord ++ tailWord_8160782) baseStart_8160782 baseEnd_8160782 := by
    simpa [prefixWord, tailWord_8160782, baseEnd_8160782] using wordTrace_append hprefix tailTrace_8160782
  have hstable : (prefixWord ++ tailWord_8160782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160782).length < 2 ^ (prefixWord ++ tailWord_8160782).sum := by decide
  have hdescent : baseEnd_8160782 < baseStart_8160782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160821 : List Nat := [1, 3, 3, 1, 1, 14]
def baseStart_8160821 : Nat := 118140960795 + 8160821 * 2 ^ 59
def prefixEnd_8160821 : Nat := 4983230072969 + 3 ^ 40 * 8160821 * 2
def baseEnd_8160821 : Nat := 17244542009487738617311

theorem tailTrace_8160821 : CollatzResearch.WordTrace tailWord_8160821 prefixEnd_8160821 17244542009487738617311 := by
  unfold tailWord_8160821
  simp only [CollatzResearch.WordTrace]
  refine ⟨297649594767746749109226317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198433063178497832739484211 297649594767746749109226317)
  ·
    refine ⟨111618598037905030915959869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297649594767746749109226317 111618598037905030915959869)
    ·
      refine ⟨41856974264214386593484951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111618598037905030915959869 41856974264214386593484951)
      ·
        refine ⟨62785461396321579890227427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41856974264214386593484951 62785461396321579890227427)
        ·
          refine ⟨94178192094482369835341141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62785461396321579890227427 94178192094482369835341141)
          ·
            refine ⟨17244542009487738617311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 94178192094482369835341141 17244542009487738617311)
            ·
              rfl

theorem cell23_8160821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 14].length) (baseStart_8160821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160821 prefixEnd_8160821 := by exact prefixLift 8160821
  have htrace : WordTrace (prefixWord ++ tailWord_8160821) baseStart_8160821 baseEnd_8160821 := by
    simpa [prefixWord, tailWord_8160821, baseEnd_8160821] using wordTrace_append hprefix tailTrace_8160821
  have hstable : (prefixWord ++ tailWord_8160821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160821).length < 2 ^ (prefixWord ++ tailWord_8160821).sum := by decide
  have hdescent : baseEnd_8160821 < baseStart_8160821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160825 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 2, 4]
def baseStart_8160825 : Nat := 118140960795 + 8160825 * 2 ^ 59
def prefixEnd_8160825 : Nat := 4983230072969 + 3 ^ 40 * 8160825 * 2
def baseEnd_8160825 : Nat := 1396808587409379489452185

theorem tailTrace_8160825 : CollatzResearch.WordTrace tailWord_8160825 prefixEnd_8160825 1396808587409379489452185 := by
  unfold tailWord_8160825
  simp only [CollatzResearch.WordTrace]
  refine ⟨297649740659732257792371929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198433160439821505194914619 297649740659732257792371929)
  ·
    refine ⟨223237305494799193344278947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297649740659732257792371929 223237305494799193344278947)
    ·
      refine ⟨334855958242198790016418421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223237305494799193344278947 334855958242198790016418421)
      ·
        refine ⟨31392746085206136564039227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334855958242198790016418421 31392746085206136564039227)
        ·
          refine ⟨47089119127809204846058841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31392746085206136564039227 47089119127809204846058841)
          ·
            refine ⟨35316839345856903634544131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47089119127809204846058841 35316839345856903634544131)
            ·
              refine ⟨52975259018785355451816197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35316839345856903634544131 52975259018785355451816197)
              ·
                refine ⟨9932861066022254147215537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52975259018785355451816197 9932861066022254147215537)
                ·
                  refine ⟨7449645799516690610411653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932861066022254147215537 7449645799516690610411653)
                  ·
                    refine ⟨1396808587409379489452185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449645799516690610411653 1396808587409379489452185)
                    ·
                      rfl

theorem cell23_8160825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_8160825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160825 prefixEnd_8160825 := by exact prefixLift 8160825
  have htrace : WordTrace (prefixWord ++ tailWord_8160825) baseStart_8160825 baseEnd_8160825 := by
    simpa [prefixWord, tailWord_8160825, baseEnd_8160825] using wordTrace_append hprefix tailTrace_8160825
  have hstable : (prefixWord ++ tailWord_8160825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160825).length < 2 ^ (prefixWord ++ tailWord_8160825).sum := by decide
  have hdescent : baseEnd_8160825 < baseStart_8160825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160841 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_8160841 : Nat := 118140960795 + 8160841 * 2 ^ 59
def prefixEnd_8160841 : Nat := 4983230072969 + 3 ^ 40 * 8160841 * 2
def baseEnd_8160841 : Nat := 4190433977918610405756481

theorem tailTrace_8160841 : CollatzResearch.WordTrace tailWord_8160841 prefixEnd_8160841 4190433977918610405756481 := by
  unfold tailWord_8160841
  simp only [CollatzResearch.WordTrace]
  refine ⟨297650324227674292524954377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198433549485116195016636251 297650324227674292524954377)
  ·
    refine ⟨223237743170755719393715783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297650324227674292524954377 223237743170755719393715783)
    ·
      refine ⟨334856614756133579090573675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223237743170755719393715783 334856614756133579090573675)
      ·
        refine ⟨502284922134200368635860513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334856614756133579090573675 502284922134200368635860513)
        ·
          refine ⟨376713691600650276476895385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502284922134200368635860513 376713691600650276476895385)
          ·
            refine ⟨282535268700487707357671539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376713691600650276476895385 282535268700487707357671539)
            ·
              refine ⟨423802903050731561036507309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282535268700487707357671539 423802903050731561036507309)
              ·
                refine ⟨158926088644024335388690241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423802903050731561036507309 158926088644024335388690241)
                ·
                  refine ⟨119194566483018251541517681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158926088644024335388690241 119194566483018251541517681)
                  ·
                    refine ⟨89395924862263688656138261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119194566483018251541517681 89395924862263688656138261)
                    ·
                      refine ⟨4190433977918610405756481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89395924862263688656138261 4190433977918610405756481)
                      ·
                        rfl

theorem cell23_8160841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_8160841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160841 prefixEnd_8160841 := by exact prefixLift 8160841
  have htrace : WordTrace (prefixWord ++ tailWord_8160841) baseStart_8160841 baseEnd_8160841 := by
    simpa [prefixWord, tailWord_8160841, baseEnd_8160841] using wordTrace_append hprefix tailTrace_8160841
  have hstable : (prefixWord ++ tailWord_8160841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160841).length < 2 ^ (prefixWord ++ tailWord_8160841).sum := by decide
  have hdescent : baseEnd_8160841 < baseStart_8160841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160865 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_8160865 : Nat := 118140960795 + 8160865 * 2 ^ 59
def prefixEnd_8160865 : Nat := 4983230072969 + 3 ^ 40 * 8160865 * 2
def baseEnd_8160865 : Nat := 4190446301454318311856371

theorem tailTrace_8160865 : CollatzResearch.WordTrace tailWord_8160865 prefixEnd_8160865 4190446301454318311856371 := by
  unfold tailWord_8160865
  simp only [CollatzResearch.WordTrace]
  refine ⟨297651199579587344623828049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198434133053058229749218699 297651199579587344623828049)
  ·
    refine ⟨223238399684690508467871037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297651199579587344623828049 223238399684690508467871037)
    ·
      refine ⟨83714399881758940675451639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223238399684690508467871037 83714399881758940675451639)
      ·
        refine ⟨125571599822638411013177459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83714399881758940675451639 125571599822638411013177459)
        ·
          refine ⟨188357399733957616519766189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125571599822638411013177459 188357399733957616519766189)
          ·
            refine ⟨70634024900234106194912321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188357399733957616519766189 70634024900234106194912321)
            ·
              refine ⟨52975518675175579646184241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70634024900234106194912321 52975518675175579646184241)
              ·
                refine ⟨39731639006381684734638181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52975518675175579646184241 39731639006381684734638181)
                ·
                  refine ⟨7449682313696565887744659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39731639006381684734638181 7449682313696565887744659)
                  ·
                    refine ⟨11174523470544848831616989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449682313696565887744659 11174523470544848831616989)
                    ·
                      refine ⟨4190446301454318311856371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174523470544848831616989 4190446301454318311856371)
                      ·
                        rfl

theorem cell23_8160865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_8160865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160865 prefixEnd_8160865 := by exact prefixLift 8160865
  have htrace : WordTrace (prefixWord ++ tailWord_8160865) baseStart_8160865 baseEnd_8160865 := by
    simpa [prefixWord, tailWord_8160865, baseEnd_8160865] using wordTrace_append hprefix tailTrace_8160865
  have hstable : (prefixWord ++ tailWord_8160865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160865).length < 2 ^ (prefixWord ++ tailWord_8160865).sum := by decide
  have hdescent : baseEnd_8160865 < baseStart_8160865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160869 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 1, 2, 3]
def baseStart_8160869 : Nat := 118140960795 + 8160869 * 2 ^ 59
def prefixEnd_8160869 : Nat := 4983230072969 + 3 ^ 40 * 8160869 * 2
def baseEnd_8160869 : Nat := 4190448355376936296206353

theorem tailTrace_8160869 : CollatzResearch.WordTrace tailWord_8160869 prefixEnd_8160869 4190448355376936296206353 := by
  unfold tailWord_8160869
  simp only [CollatzResearch.WordTrace]
  refine ⟨297651345471572853306973661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198434230314381902204649107 297651345471572853306973661)
  ·
    refine ⟨111619254551839819990115123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297651345471572853306973661 111619254551839819990115123)
    ·
      refine ⟨167428881827759729985172685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111619254551839819990115123 167428881827759729985172685)
      ·
        refine ⟨62785830685409898744439757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167428881827759729985172685 62785830685409898744439757)
        ·
          refine ⟨23544686507028712029164909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62785830685409898744439757 23544686507028712029164909)
          ·
            refine ⟨8829257440135767010936841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23544686507028712029164909 8829257440135767010936841)
            ·
              refine ⟨6621943080101825258202631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829257440135767010936841 6621943080101825258202631)
              ·
                refine ⟨9932914620152737887303947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621943080101825258202631 9932914620152737887303947)
                ·
                  refine ⟨14899371930229106830955921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9932914620152737887303947 14899371930229106830955921)
                  ·
                    refine ⟨11174528947671830123216941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14899371930229106830955921 11174528947671830123216941)
                    ·
                      refine ⟨4190448355376936296206353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174528947671830123216941 4190448355376936296206353)
                      ·
                        rfl

theorem cell23_8160869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_8160869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160869 prefixEnd_8160869 := by exact prefixLift 8160869
  have htrace : WordTrace (prefixWord ++ tailWord_8160869) baseStart_8160869 baseEnd_8160869 := by
    simpa [prefixWord, tailWord_8160869, baseEnd_8160869] using wordTrace_append hprefix tailTrace_8160869
  have hstable : (prefixWord ++ tailWord_8160869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160869).length < 2 ^ (prefixWord ++ tailWord_8160869).sum := by decide
  have hdescent : baseEnd_8160869 < baseStart_8160869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160882 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_8160882 : Nat := 118140960795 + 8160882 * 2 ^ 59
def prefixEnd_8160882 : Nat := 4983230072969 + 3 ^ 40 * 8160882 * 2
def baseEnd_8160882 : Nat := 4190455030625444745343793

theorem tailTrace_8160882 : CollatzResearch.WordTrace tailWord_8160882 prefixEnd_8160882 4190455030625444745343793 := by
  unfold tailWord_8160882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74412954905131439131799225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198434546413683837684797933 74412954905131439131799225)
  ·
    refine ⟨55809716178848579348849419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74412954905131439131799225 55809716178848579348849419)
    ·
      refine ⟨83714574268272869023274129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55809716178848579348849419 83714574268272869023274129)
      ·
        refine ⟨62785930701204651767455597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83714574268272869023274129 62785930701204651767455597)
        ·
          refine ⟨23544724012951744412795849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62785930701204651767455597 23544724012951744412795849)
          ·
            refine ⟨17658543009713808309596887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23544724012951744412795849 17658543009713808309596887)
            ·
              refine ⟨26487814514570712464395331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17658543009713808309596887 26487814514570712464395331)
              ·
                refine ⟨39731721771856068696592997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26487814514570712464395331 39731721771856068696592997)
                ·
                  refine ⟨7449697832223012880611187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39731721771856068696592997 7449697832223012880611187)
                  ·
                    refine ⟨11174546748334519320916781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449697832223012880611187 11174546748334519320916781)
                    ·
                      refine ⟨4190455030625444745343793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174546748334519320916781 4190455030625444745343793)
                      ·
                        rfl

theorem cell23_8160882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_8160882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160882 prefixEnd_8160882 := by exact prefixLift 8160882
  have htrace : WordTrace (prefixWord ++ tailWord_8160882) baseStart_8160882 baseEnd_8160882 := by
    simpa [prefixWord, tailWord_8160882, baseEnd_8160882] using wordTrace_append hprefix tailTrace_8160882
  have hstable : (prefixWord ++ tailWord_8160882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160882).length < 2 ^ (prefixWord ++ tailWord_8160882).sum := by decide
  have hdescent : baseEnd_8160882 < baseStart_8160882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160908 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_8160908 : Nat := 118140960795 + 8160908 * 2 ^ 59
def prefixEnd_8160908 : Nat := 4983230072969 + 3 ^ 40 * 8160908 * 2
def baseEnd_8160908 : Nat := 4190468381122461643618673

theorem tailTrace_8160908 : CollatzResearch.WordTrace tailWord_8160908 prefixEnd_8160908 4190468381122461643618673 := by
  unfold tailWord_8160908
  simp only [CollatzResearch.WordTrace]
  refine ⟨148826383959215781483821689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198435178612287708645095585 148826383959215781483821689)
  ·
    refine ⟨111619787969411836112866267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148826383959215781483821689 111619787969411836112866267)
    ·
      refine ⟨167429681954117754169299401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111619787969411836112866267 167429681954117754169299401)
      ·
        refine ⟨125572261465588315626974551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167429681954117754169299401 125572261465588315626974551)
        ·
          refine ⟨188358392198382473440461827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125572261465588315626974551 188358392198382473440461827)
          ·
            refine ⟨282537588297573710160692741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188358392198382473440461827 282537588297573710160692741)
            ·
              refine ⟨52975797805795070655129889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282537588297573710160692741 52975797805795070655129889)
              ·
                refine ⟨39731848354346302991347417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52975797805795070655129889 39731848354346302991347417)
                ·
                  refine ⟨29798886265759727243510563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39731848354346302991347417 29798886265759727243510563)
                  ·
                    refine ⟨44698329398639590865265845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29798886265759727243510563 44698329398639590865265845)
                    ·
                      refine ⟨4190468381122461643618673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44698329398639590865265845 4190468381122461643618673)
                      ·
                        rfl

theorem cell23_8160908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_8160908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160908 prefixEnd_8160908 := by exact prefixLift 8160908
  have htrace : WordTrace (prefixWord ++ tailWord_8160908) baseStart_8160908 baseEnd_8160908 := by
    simpa [prefixWord, tailWord_8160908, baseEnd_8160908] using wordTrace_append hprefix tailTrace_8160908
  have hstable : (prefixWord ++ tailWord_8160908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160908).length < 2 ^ (prefixWord ++ tailWord_8160908).sum := by decide
  have hdescent : baseEnd_8160908 < baseStart_8160908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160956 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_8160956 : Nat := 118140960795 + 8160956 * 2 ^ 59
def prefixEnd_8160956 : Nat := 4983230072969 + 3 ^ 40 * 8160956 * 2
def baseEnd_8160956 : Nat := 4190493028193877455818453

theorem tailTrace_8160956 : CollatzResearch.WordTrace tailWord_8160956 prefixEnd_8160956 4190493028193877455818453 := by
  unfold tailWord_8160956
  simp only [CollatzResearch.WordTrace]
  refine ⟨148827259311128833582695361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198436345748171778110260481 148827259311128833582695361)
  ·
    refine ⟨111620444483346625187021521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148827259311128833582695361 111620444483346625187021521)
    ·
      refine ⟨83715333362509968890266141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111620444483346625187021521 83715333362509968890266141)
      ·
        refine ⟨31393250010941238333849803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83715333362509968890266141 31393250010941238333849803)
        ·
          refine ⟨47089875016411857500774705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31393250010941238333849803 47089875016411857500774705)
          ·
            refine ⟨35317406262308893125581029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47089875016411857500774705 35317406262308893125581029)
            ·
              refine ⟨6622013674182917461046443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35317406262308893125581029 6622013674182917461046443)
              ·
                refine ⟨9933020511274376191569665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622013674182917461046443 9933020511274376191569665)
                ·
                  refine ⟨7449765383455782143677249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9933020511274376191569665 7449765383455782143677249)
                  ·
                    refine ⟨5587324037591836607757937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7449765383455782143677249 5587324037591836607757937)
                    ·
                      refine ⟨4190493028193877455818453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587324037591836607757937 4190493028193877455818453)
                      ·
                        rfl

theorem cell23_8160956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_8160956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160956 prefixEnd_8160956 := by exact prefixLift 8160956
  have htrace : WordTrace (prefixWord ++ tailWord_8160956) baseStart_8160956 baseEnd_8160956 := by
    simpa [prefixWord, tailWord_8160956, baseEnd_8160956] using wordTrace_append hprefix tailTrace_8160956
  have hstable : (prefixWord ++ tailWord_8160956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160956).length < 2 ^ (prefixWord ++ tailWord_8160956).sum := by decide
  have hdescent : baseEnd_8160956 < baseStart_8160956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160965 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 2, 5, 2]
def baseStart_8160965 : Nat := 118140960795 + 8160965 * 2 ^ 59
def prefixEnd_8160965 : Nat := 4983230072969 + 3 ^ 40 * 8160965 * 2
def baseEnd_8160965 : Nat := 4190497649519767920605911

theorem tailTrace_8160965 : CollatzResearch.WordTrace tailWord_8160965 prefixEnd_8160965 4190497649519767920605911 := by
  unfold tailWord_8160965
  simp only [CollatzResearch.WordTrace]
  refine ⟨297654846879225061702468349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198436564586150041134978899 297654846879225061702468349)
  ·
    refine ⟨111620567579709398138425631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297654846879225061702468349 111620567579709398138425631)
    ·
      refine ⟨167430851369564097207638447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111620567579709398138425631 167430851369564097207638447)
      ·
        refine ⟨251146277054346145811457671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167430851369564097207638447 251146277054346145811457671)
        ·
          refine ⟨376719415581519218717186507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251146277054346145811457671 376719415581519218717186507)
          ·
            refine ⟨565079123372278828075779761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376719415581519218717186507 565079123372278828075779761)
            ·
              refine ⟨423809342529209121056834821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565079123372278828075779761 423809342529209121056834821)
              ·
                refine ⟨79464251724226710198156529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423809342529209121056834821 79464251724226710198156529)
                ·
                  refine ⟨59598188793170032648617397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79464251724226710198156529 59598188793170032648617397)
                  ·
                    refine ⟨5587330199359690560807881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59598188793170032648617397 5587330199359690560807881)
                    ·
                      refine ⟨4190497649519767920605911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587330199359690560807881 4190497649519767920605911)
                      ·
                        rfl

theorem cell23_8160965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_8160965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160965 prefixEnd_8160965 := by exact prefixLift 8160965
  have htrace : WordTrace (prefixWord ++ tailWord_8160965) baseStart_8160965 baseEnd_8160965 := by
    simpa [prefixWord, tailWord_8160965, baseEnd_8160965] using wordTrace_append hprefix tailTrace_8160965
  have hstable : (prefixWord ++ tailWord_8160965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160965).length < 2 ^ (prefixWord ++ tailWord_8160965).sum := by decide
  have hdescent : baseEnd_8160965 < baseStart_8160965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8160968 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_8160968 : Nat := 118140960795 + 8160968 * 2 ^ 59
def prefixEnd_8160968 : Nat := 4983230072969 + 3 ^ 40 * 8160968 * 2
def baseEnd_8160968 : Nat := 4190499189961731408868397

theorem tailTrace_8160968 : CollatzResearch.WordTrace tailWord_8160968 prefixEnd_8160968 4190499189961731408868397 := by
  unfold tailWord_8160968
  simp only [CollatzResearch.WordTrace]
  refine ⟨148827478149107096607413779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198436637532142795476551705 148827478149107096607413779)
  ·
    refine ⟨223241217223660644911120669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148827478149107096607413779 223241217223660644911120669)
    ·
      refine ⟨83715456458872741841670251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223241217223660644911120669 83715456458872741841670251)
      ·
        refine ⟨125573184688309112762505377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83715456458872741841670251 125573184688309112762505377)
        ·
          refine ⟨94179888516231834571879033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125573184688309112762505377 94179888516231834571879033)
          ·
            refine ⟨70634916387173875928909275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94179888516231834571879033 70634916387173875928909275)
            ·
              refine ⟨105952374580760813893363913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70634916387173875928909275 105952374580760813893363913)
              ·
                refine ⟨79464280935570610420022935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105952374580760813893363913 79464280935570610420022935)
                ·
                  refine ⟨119196421403355915630034403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79464280935570610420022935 119196421403355915630034403)
                  ·
                    refine ⟨178794632105033873445051605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119196421403355915630034403 178794632105033873445051605)
                    ·
                      refine ⟨4190499189961731408868397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178794632105033873445051605 4190499189961731408868397)
                      ·
                        rfl

theorem cell23_8160968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_8160968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8160968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8160968 prefixEnd_8160968 := by exact prefixLift 8160968
  have htrace : WordTrace (prefixWord ++ tailWord_8160968) baseStart_8160968 baseEnd_8160968 := by
    simpa [prefixWord, tailWord_8160968, baseEnd_8160968] using wordTrace_append hprefix tailTrace_8160968
  have hstable : (prefixWord ++ tailWord_8160968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8160968).length < 2 ^ (prefixWord ++ tailWord_8160968).sum := by decide
  have hdescent : baseEnd_8160968 < baseStart_8160968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8160968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161008 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_8161008 : Nat := 118140960795 + 8161008 * 2 ^ 59
def prefixEnd_8161008 : Nat := 4983230072969 + 3 ^ 40 * 8161008 * 2
def baseEnd_8161008 : Nat := 4190519729187911252368213

theorem tailTrace_8161008 : CollatzResearch.WordTrace tailWord_8161008 prefixEnd_8161008 4190519729187911252368213 := by
  unfold tailWord_8161008
  simp only [CollatzResearch.WordTrace]
  refine ⟨148828207609034640023141839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198437610145379520030855785 148828207609034640023141839)
  ·
    refine ⟨223242311413551960034712759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148828207609034640023141839 223242311413551960034712759)
    ·
      refine ⟨334863467120327940052069139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223242311413551960034712759 334863467120327940052069139)
      ·
        refine ⟨502295200680491910078103709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334863467120327940052069139 502295200680491910078103709)
        ·
          refine ⟨188360700255184466279288891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502295200680491910078103709 188360700255184466279288891)
          ·
            refine ⟨282541050382776699418933337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188360700255184466279288891 282541050382776699418933337)
            ·
              refine ⟨211905787787082524564200003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282541050382776699418933337 211905787787082524564200003)
              ·
                refine ⟨317858681680623786846300005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211905787787082524564200003 317858681680623786846300005)
                ·
                  refine ⟨59598502815116960033681251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317858681680623786846300005 59598502815116960033681251)
                  ·
                    refine ⟨89397754222675440050521877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59598502815116960033681251 89397754222675440050521877)
                    ·
                      refine ⟨4190519729187911252368213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89397754222675440050521877 4190519729187911252368213)
                      ·
                        rfl

theorem cell23_8161008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_8161008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161008 prefixEnd_8161008 := by exact prefixLift 8161008
  have htrace : WordTrace (prefixWord ++ tailWord_8161008) baseStart_8161008 baseEnd_8161008 := by
    simpa [prefixWord, tailWord_8161008, baseEnd_8161008] using wordTrace_append hprefix tailTrace_8161008
  have hstable : (prefixWord ++ tailWord_8161008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161008).length < 2 ^ (prefixWord ++ tailWord_8161008).sum := by decide
  have hdescent : baseEnd_8161008 < baseStart_8161008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161015 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_8161015 : Nat := 118140960795 + 8161015 * 2 ^ 59
def prefixEnd_8161015 : Nat := 4983230072969 + 3 ^ 40 * 8161015 * 2
def baseEnd_8161015 : Nat := 4190523323552492724980681

theorem tailTrace_8161015 : CollatzResearch.WordTrace tailWord_8161015 prefixEnd_8161015 4190523323552492724980681 := by
  unfold tailWord_8161015
  simp only [CollatzResearch.WordTrace]
  refine ⟨297656670529043920241788499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198437780352695946827858999 297656670529043920241788499)
  ·
    refine ⟨446485005793565880362682749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297656670529043920241788499 446485005793565880362682749)
    ·
      refine ⟨167431877172587205136006031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446485005793565880362682749 167431877172587205136006031)
      ·
        refine ⟨251147815758880807704009047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167431877172587205136006031 251147815758880807704009047)
        ·
          refine ⟨376721723638321211556013571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251147815758880807704009047 376721723638321211556013571)
          ·
            refine ⟨565082585457481817334020357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376721723638321211556013571 565082585457481817334020357)
            ·
              refine ⟨105952984773277840750128817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565082585457481817334020357 105952984773277840750128817)
              ·
                refine ⟨79464738579958380562596613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105952984773277840750128817 79464738579958380562596613)
                ·
                  refine ⟨14899638483742196355486865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79464738579958380562596613 14899638483742196355486865)
                  ·
                    refine ⟨11174728862806647266615149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14899638483742196355486865 11174728862806647266615149)
                    ·
                      refine ⟨4190523323552492724980681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174728862806647266615149 4190523323552492724980681)
                      ·
                        rfl

theorem cell23_8161015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_8161015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161015 prefixEnd_8161015 := by exact prefixLift 8161015
  have htrace : WordTrace (prefixWord ++ tailWord_8161015) baseStart_8161015 baseEnd_8161015 := by
    simpa [prefixWord, tailWord_8161015, baseEnd_8161015] using wordTrace_append hprefix tailTrace_8161015
  have hstable : (prefixWord ++ tailWord_8161015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161015).length < 2 ^ (prefixWord ++ tailWord_8161015).sum := by decide
  have hdescent : baseEnd_8161015 < baseStart_8161015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161018 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_8161018 : Nat := 118140960795 + 8161018 * 2 ^ 59
def prefixEnd_8161018 : Nat := 4983230072969 + 3 ^ 40 * 8161018 * 2
def baseEnd_8161018 : Nat := 465613873777161801471463

theorem tailTrace_8161018 : CollatzResearch.WordTrace tailWord_8161018 prefixEnd_8161018 465613873777161801471463 := by
  unfold tailWord_8161018
  simp only [CollatzResearch.WordTrace]
  refine ⟨74414194987008262938536927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198437853298688701169431805 74414194987008262938536927)
  ·
    refine ⟨111621292480512394407805391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74414194987008262938536927 111621292480512394407805391)
    ·
      refine ⟨167431938720768591611708087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111621292480512394407805391 167431938720768591611708087)
      ·
        refine ⟨251147908081152887417562131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167431938720768591611708087 251147908081152887417562131)
        ·
          refine ⟨376721862121729331126343197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251147908081152887417562131 376721862121729331126343197)
          ·
            refine ⟨141270698295648499172378699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376721862121729331126343197 141270698295648499172378699)
            ·
              refine ⟨211906047443472748758568049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141270698295648499172378699 211906047443472748758568049)
              ·
                refine ⟨158929535582604561568926037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211906047443472748758568049 158929535582604561568926037)
                ·
                  refine ⟨465613873777161801471463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 158929535582604561568926037 465613873777161801471463)
                  ·
                    rfl

theorem cell23_8161018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_8161018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161018 prefixEnd_8161018 := by exact prefixLift 8161018
  have htrace : WordTrace (prefixWord ++ tailWord_8161018) baseStart_8161018 baseEnd_8161018 := by
    simpa [prefixWord, tailWord_8161018, baseEnd_8161018] using wordTrace_append hprefix tailTrace_8161018
  have hstable : (prefixWord ++ tailWord_8161018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161018).length < 2 ^ (prefixWord ++ tailWord_8161018).sum := by decide
  have hdescent : baseEnd_8161018 < baseStart_8161018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161042 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_8161042 : Nat := 118140960795 + 8161042 * 2 ^ 59
def prefixEnd_8161042 : Nat := 4983230072969 + 3 ^ 40 * 8161042 * 2
def baseEnd_8161042 : Nat := 4190537187530164119343057

theorem tailTrace_8161042 : CollatzResearch.WordTrace tailWord_8161042 prefixEnd_8161042 4190537187530164119343057 := by
  unfold tailWord_8161042
  simp only [CollatzResearch.WordTrace]
  refine ⟨74414413824986525963255345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198438436866630735902014253 74414413824986525963255345)
  ·
    refine ⟨55810810368739894472441509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74414413824986525963255345 55810810368739894472441509)
    ·
      refine ⟨10464526944138730213582783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55810810368739894472441509 10464526944138730213582783)
      ·
        refine ⟨15696790416208095320374175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10464526944138730213582783 15696790416208095320374175)
        ·
          refine ⟨23545185624312142980561263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15696790416208095320374175 23545185624312142980561263)
          ·
            refine ⟨35317778436468214470841895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23545185624312142980561263 35317778436468214470841895)
            ·
              refine ⟨52976667654702321706262843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35317778436468214470841895 52976667654702321706262843)
              ·
                refine ⟨79465001482053482559394265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52976667654702321706262843 79465001482053482559394265)
                ·
                  refine ⟨59598751111540111919545699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79465001482053482559394265 59598751111540111919545699)
                  ·
                    refine ⟨89398126667310167879318549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59598751111540111919545699 89398126667310167879318549)
                    ·
                      refine ⟨4190537187530164119343057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89398126667310167879318549 4190537187530164119343057)
                      ·
                        rfl

theorem cell23_8161042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_8161042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161042 prefixEnd_8161042 := by exact prefixLift 8161042
  have htrace : WordTrace (prefixWord ++ tailWord_8161042) baseStart_8161042 baseEnd_8161042 := by
    simpa [prefixWord, tailWord_8161042, baseEnd_8161042] using wordTrace_append hprefix tailTrace_8161042
  have hstable : (prefixWord ++ tailWord_8161042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161042).length < 2 ^ (prefixWord ++ tailWord_8161042).sum := by decide
  have hdescent : baseEnd_8161042 < baseStart_8161042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161082 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_8161082 : Nat := 118140960795 + 8161082 * 2 ^ 59
def prefixEnd_8161082 : Nat := 4983230072969 + 3 ^ 40 * 8161082 * 2
def baseEnd_8161082 : Nat := 1396852575585447987614291

theorem tailTrace_8161082 : CollatzResearch.WordTrace tailWord_8161082 prefixEnd_8161082 1396852575585447987614291 := by
  unfold tailWord_8161082
  simp only [CollatzResearch.WordTrace]
  refine ⟨74414778554950297671119375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198439409479867460456318333 74414778554950297671119375)
  ·
    refine ⟨111622167832425446506679063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74414778554950297671119375 111622167832425446506679063)
    ·
      refine ⟨167433251748638169760018595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111622167832425446506679063 167433251748638169760018595)
      ·
        refine ⟨251149877622957254640027893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167433251748638169760018595 251149877622957254640027893)
        ·
          refine ⟨23545301027152242622502615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251149877622957254640027893 23545301027152242622502615)
          ·
            refine ⟨35317951540728363933753923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23545301027152242622502615 35317951540728363933753923)
            ·
              refine ⟨52976927311092545900630885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35317951540728363933753923 52976927311092545900630885)
              ·
                refine ⟨9933173870829852356368291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52976927311092545900630885 9933173870829852356368291)
                ·
                  refine ⟨14899760806244778534552437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9933173870829852356368291 14899760806244778534552437)
                  ·
                    refine ⟨1396852575585447987614291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14899760806244778534552437 1396852575585447987614291)
                    ·
                      rfl

theorem cell23_8161082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_8161082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161082 prefixEnd_8161082 := by exact prefixLift 8161082
  have htrace : WordTrace (prefixWord ++ tailWord_8161082) baseStart_8161082 baseEnd_8161082 := by
    simpa [prefixWord, tailWord_8161082, baseEnd_8161082] using wordTrace_append hprefix tailTrace_8161082
  have hstable : (prefixWord ++ tailWord_8161082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161082).length < 2 ^ (prefixWord ++ tailWord_8161082).sum := by decide
  have hdescent : baseEnd_8161082 < baseStart_8161082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161095 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 1, 6]
def baseStart_8161095 : Nat := 118140960795 + 8161095 * 2 ^ 59
def prefixEnd_8161095 : Nat := 4983230072969 + 3 ^ 40 * 8161095 * 2
def baseEnd_8161095 : Nat := 1396854800668284137326771

theorem tailTrace_8161095 : CollatzResearch.WordTrace tailWord_8161095 prefixEnd_8161095 1396854800668284137326771 := by
  unfold tailWord_8161095
  simp only [CollatzResearch.WordTrace]
  refine ⟨297659588368754093904700739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198439725579169395936467159 297659588368754093904700739)
  ·
    refine ⟨446489382553131140857051109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297659588368754093904700739 446489382553131140857051109)
    ·
      refine ⟨83716759228712088910697083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446489382553131140857051109 83716759228712088910697083)
      ·
        refine ⟨125575138843068133366045625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83716759228712088910697083 125575138843068133366045625)
        ·
          refine ⟨94181354132301100024534219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125575138843068133366045625 94181354132301100024534219)
          ·
            refine ⟨141272031198451650036801329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94181354132301100024534219 141272031198451650036801329)
            ·
              refine ⟨105954023398838737527600997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141272031198451650036801329 105954023398838737527600997)
              ·
                refine ⟨19866379387282263286425187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105954023398838737527600997 19866379387282263286425187)
                ·
                  refine ⟨29799569080923394929637781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19866379387282263286425187 29799569080923394929637781)
                  ·
                    refine ⟨1396854800668284137326771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29799569080923394929637781 1396854800668284137326771)
                    ·
                      rfl

theorem cell23_8161095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_8161095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161095 prefixEnd_8161095 := by exact prefixLift 8161095
  have htrace : WordTrace (prefixWord ++ tailWord_8161095) baseStart_8161095 baseEnd_8161095 := by
    simpa [prefixWord, tailWord_8161095, baseEnd_8161095] using wordTrace_append hprefix tailTrace_8161095
  have hstable : (prefixWord ++ tailWord_8161095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161095).length < 2 ^ (prefixWord ++ tailWord_8161095).sum := by decide
  have hdescent : baseEnd_8161095 < baseStart_8161095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161096 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_8161096 : Nat := 118140960795 + 8161096 * 2 ^ 59
def prefixEnd_8161096 : Nat := 4983230072969 + 3 ^ 40 * 8161096 * 2
def baseEnd_8161096 : Nat := 4190564915485506908067809

theorem tailTrace_8161096 : CollatzResearch.WordTrace tailWord_8161096 prefixEnd_8161096 4190564915485506908067809 := by
  unfold tailWord_8161096
  simp only [CollatzResearch.WordTrace]
  refine ⟨148829812420875235537743571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198439749894500314050324761 148829812420875235537743571)
  ·
    refine ⟨223244718631312853306615357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148829812420875235537743571 223244718631312853306615357)
    ·
      refine ⟨83716769486742319989980759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223244718631312853306615357 83716769486742319989980759)
      ·
        refine ⟨125575154230113479984971139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83716769486742319989980759 125575154230113479984971139)
        ·
          refine ⟨188362731345170219977456709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125575154230113479984971139 188362731345170219977456709)
          ·
            refine ⟨35318012127219416245773133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188362731345170219977456709 35318012127219416245773133)
            ·
              refine ⟨13244254547707281092164925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35318012127219416245773133 13244254547707281092164925)
              ·
                refine ⟨4966595455390230409561847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13244254547707281092164925 4966595455390230409561847)
                ·
                  refine ⟨7449893183085345614342771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966595455390230409561847 7449893183085345614342771)
                  ·
                    refine ⟨11174839774628018421514157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449893183085345614342771 11174839774628018421514157)
                    ·
                      refine ⟨4190564915485506908067809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174839774628018421514157 4190564915485506908067809)
                      ·
                        rfl

theorem cell23_8161096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_8161096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161096 prefixEnd_8161096 := by exact prefixLift 8161096
  have htrace : WordTrace (prefixWord ++ tailWord_8161096) baseStart_8161096 baseEnd_8161096 := by
    simpa [prefixWord, tailWord_8161096, baseEnd_8161096] using wordTrace_append hprefix tailTrace_8161096
  have hstable : (prefixWord ++ tailWord_8161096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161096).length < 2 ^ (prefixWord ++ tailWord_8161096).sum := by decide
  have hdescent : baseEnd_8161096 < baseStart_8161096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161152 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_8161152 : Nat := 118140960795 + 8161152 * 2 ^ 59
def prefixEnd_8161152 : Nat := 4983230072969 + 3 ^ 40 * 8161152 * 2
def baseEnd_8161152 : Nat := 4190593670402158688967551

theorem tailTrace_8161152 : CollatzResearch.WordTrace tailWord_8161152 prefixEnd_8161152 4190593670402158688967551 := by
  unfold tailWord_8161152
  simp only [CollatzResearch.WordTrace]
  refine ⟨148830833664773796319762855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198441111553031728426350473 148830833664773796319762855)
  ·
    refine ⟨223246250497160694479644283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148830833664773796319762855 223246250497160694479644283)
    ·
      refine ⟨334869375745741041719466425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223246250497160694479644283 334869375745741041719466425)
      ·
        refine ⟨251152031809305781289599819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334869375745741041719466425 251152031809305781289599819)
        ·
          refine ⟨376728047713958671934399729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251152031809305781289599819 376728047713958671934399729)
          ·
            refine ⟨282546035785469003950799797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376728047713958671934399729 282546035785469003950799797)
            ·
              refine ⟨26488690854887719120387481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282546035785469003950799797 26488690854887719120387481)
              ·
                refine ⟨19866518141165789340290611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26488690854887719120387481 19866518141165789340290611)
                ·
                  refine ⟨29799777211748684010435917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19866518141165789340290611 29799777211748684010435917)
                  ·
                    refine ⟨11174916454405756503913469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29799777211748684010435917 11174916454405756503913469)
                    ·
                      refine ⟨4190593670402158688967551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174916454405756503913469 4190593670402158688967551)
                      ·
                        rfl

theorem cell23_8161152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_8161152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161152 prefixEnd_8161152 := by exact prefixLift 8161152
  have htrace : WordTrace (prefixWord ++ tailWord_8161152) baseStart_8161152 baseEnd_8161152 := by
    simpa [prefixWord, tailWord_8161152, baseEnd_8161152] using wordTrace_append hprefix tailTrace_8161152
  have hstable : (prefixWord ++ tailWord_8161152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161152).length < 2 ^ (prefixWord ++ tailWord_8161152).sum := by decide
  have hdescent : baseEnd_8161152 < baseStart_8161152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161153 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_8161153 : Nat := 118140960795 + 8161153 * 2 ^ 59
def prefixEnd_8161153 : Nat := 4983230072969 + 3 ^ 40 * 8161153 * 2
def baseEnd_8161153 : Nat := 4190594183882813185055047

theorem tailTrace_8161153 : CollatzResearch.WordTrace tailWord_8161153 prefixEnd_8161153 4190594183882813185055047 := by
  unfold tailWord_8161153
  simp only [CollatzResearch.WordTrace]
  refine ⟨297661703802543969810312113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198441135868362646540208075 297661703802543969810312113)
  ·
    refine ⟨223246277851907977357734085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297661703802543969810312113 223246277851907977357734085)
    ·
      refine ⟨41858677097232745754575141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223246277851907977357734085 41858677097232745754575141)
      ·
        refine ⟨7848501955731139828982839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41858677097232745754575141 7848501955731139828982839)
        ·
          refine ⟨11772752933596709743474259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848501955731139828982839 11772752933596709743474259)
          ·
            refine ⟨17659129400395064615211389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772752933596709743474259 17659129400395064615211389)
            ·
              refine ⟨6622173525148149230704271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17659129400395064615211389 6622173525148149230704271)
              ·
                refine ⟨9933260287722223846056407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622173525148149230704271 9933260287722223846056407)
                ·
                  refine ⟨14899890431583335769084611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9933260287722223846056407 14899890431583335769084611)
                  ·
                    refine ⟨22349835647375003653626917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14899890431583335769084611 22349835647375003653626917)
                    ·
                      refine ⟨4190594183882813185055047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22349835647375003653626917 4190594183882813185055047)
                      ·
                        rfl

theorem cell23_8161153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_8161153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161153 prefixEnd_8161153 := by exact prefixLift 8161153
  have htrace : WordTrace (prefixWord ++ tailWord_8161153) baseStart_8161153 baseEnd_8161153 := by
    simpa [prefixWord, tailWord_8161153, baseEnd_8161153] using wordTrace_append hprefix tailTrace_8161153
  have hstable : (prefixWord ++ tailWord_8161153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161153).length < 2 ^ (prefixWord ++ tailWord_8161153).sum := by decide
  have hdescent : baseEnd_8161153 < baseStart_8161153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161169 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_8161169 : Nat := 118140960795 + 8161169 * 2 ^ 59
def prefixEnd_8161169 : Nat := 4983230072969 + 3 ^ 40 * 8161169 * 2
def baseEnd_8161169 : Nat := 4190602399573285122454973

theorem tailTrace_8161169 : CollatzResearch.WordTrace tailWord_8161169 prefixEnd_8161169 4190602399573285122454973 := by
  unfold tailWord_8161169
  simp only [CollatzResearch.WordTrace]
  refine ⟨297662287370486004542894561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198441524913657336361929707 297662287370486004542894561)
  ·
    refine ⟨223246715527864503407170921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297662287370486004542894561 223246715527864503407170921)
    ·
      refine ⟨167435036645898377555378191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223246715527864503407170921 167435036645898377555378191)
      ·
        refine ⟨251152554968847566333067287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167435036645898377555378191 251152554968847566333067287)
        ·
          refine ⟨376728832453271349499600931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251152554968847566333067287 376728832453271349499600931)
          ·
            refine ⟨565093248679907024249401397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376728832453271349499600931 565093248679907024249401397)
            ·
              refine ⟨52977492063741283523381381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565093248679907024249401397 52977492063741283523381381)
              ·
                refine ⟨9933279761951490660634009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52977492063741283523381381 9933279761951490660634009)
                ·
                  refine ⟨7449959821463617995475507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9933279761951490660634009 7449959821463617995475507)
                  ·
                    refine ⟨11174939732195426993213261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449959821463617995475507 11174939732195426993213261)
                    ·
                      refine ⟨4190602399573285122454973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174939732195426993213261 4190602399573285122454973)
                      ·
                        rfl

theorem cell23_8161169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_8161169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161169 prefixEnd_8161169 := by exact prefixLift 8161169
  have htrace : WordTrace (prefixWord ++ tailWord_8161169) baseStart_8161169 baseEnd_8161169 := by
    simpa [prefixWord, tailWord_8161169, baseEnd_8161169] using wordTrace_append hprefix tailTrace_8161169
  have hstable : (prefixWord ++ tailWord_8161169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161169).length < 2 ^ (prefixWord ++ tailWord_8161169).sum := by decide
  have hdescent : baseEnd_8161169 < baseStart_8161169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161170 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_8161170 : Nat := 118140960795 + 8161170 * 2 ^ 59
def prefixEnd_8161170 : Nat := 4983230072969 + 3 ^ 40 * 8161170 * 2
def baseEnd_8161170 : Nat := 4190602913053939618542469

theorem tailTrace_8161170 : CollatzResearch.WordTrace tailWord_8161170 prefixEnd_8161170 4190602913053939618542469 := by
  unfold tailWord_8161170
  simp only [CollatzResearch.WordTrace]
  refine ⟨74415580960870595428420241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198441549228988254475787309 74415580960870595428420241)
  ·
    refine ⟨55811685720652946571315181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74415580960870595428420241 55811685720652946571315181)
    ·
      refine ⟨20929382145244854964243193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55811685720652946571315181 20929382145244854964243193)
      ·
        refine ⟨15697036608933641223182395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20929382145244854964243193 15697036608933641223182395)
        ·
          refine ⟨23545554913400461834773593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15697036608933641223182395 23545554913400461834773593)
          ·
            refine ⟨17659166185050346376080195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23545554913400461834773593 17659166185050346376080195)
            ·
              refine ⟨26488749277575519564120293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17659166185050346376080195 26488749277575519564120293)
              ·
                refine ⟨4966640489545409918272555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26488749277575519564120293 4966640489545409918272555)
                ·
                  refine ⟨7449960734318114877408833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966640489545409918272555 7449960734318114877408833)
                  ·
                    refine ⟨5587470550738586158056625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7449960734318114877408833 5587470550738586158056625)
                    ·
                      refine ⟨4190602913053939618542469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587470550738586158056625 4190602913053939618542469)
                      ·
                        rfl

theorem cell23_8161170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_8161170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161170 prefixEnd_8161170 := by exact prefixLift 8161170
  have htrace : WordTrace (prefixWord ++ tailWord_8161170) baseStart_8161170 baseEnd_8161170 := by
    simpa [prefixWord, tailWord_8161170, baseEnd_8161170] using wordTrace_append hprefix tailTrace_8161170
  have hstable : (prefixWord ++ tailWord_8161170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161170).length < 2 ^ (prefixWord ++ tailWord_8161170).sum := by decide
  have hdescent : baseEnd_8161170 < baseStart_8161170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161172 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_8161172 : Nat := 118140960795 + 8161172 * 2 ^ 59
def prefixEnd_8161172 : Nat := 4983230072969 + 3 ^ 40 * 8161172 * 2
def baseEnd_8161172 : Nat := 1396867980005082870239153

theorem tailTrace_8161172 : CollatzResearch.WordTrace tailWord_8161172 prefixEnd_8161172 1396867980005082870239153 := by
  unfold tailWord_8161172
  simp only [CollatzResearch.WordTrace]
  refine ⟨148831198394737568027626885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198441597859650090703502513 148831198394737568027626885)
  ·
    refine ⟨27905849699013294005180041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148831198394737568027626885 27905849699013294005180041)
    ·
      refine ⟨20929387274259970503885031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27905849699013294005180041 20929387274259970503885031)
      ·
        refine ⟨31394080911389955755827547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20929387274259970503885031 31394080911389955755827547)
        ·
          refine ⟨47091121367084933633741321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31394080911389955755827547 47091121367084933633741321)
          ·
            refine ⟨35318341025313700225305991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47091121367084933633741321 35318341025313700225305991)
            ·
              refine ⟨52977511537970550337958987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35318341025313700225305991 52977511537970550337958987)
              ·
                refine ⟨79466267306955825506938481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52977511537970550337958987 79466267306955825506938481)
                ·
                  refine ⟨59599700480216869130203861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79466267306955825506938481 59599700480216869130203861)
                  ·
                    refine ⟨1396867980005082870239153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59599700480216869130203861 1396867980005082870239153)
                    ·
                      rfl

theorem cell23_8161172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_8161172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161172 prefixEnd_8161172 := by exact prefixLift 8161172
  have htrace : WordTrace (prefixWord ++ tailWord_8161172) baseStart_8161172 baseEnd_8161172 := by
    simpa [prefixWord, tailWord_8161172, baseEnd_8161172] using wordTrace_append hprefix tailTrace_8161172
  have hstable : (prefixWord ++ tailWord_8161172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161172).length < 2 ^ (prefixWord ++ tailWord_8161172).sum := by decide
  have hdescent : baseEnd_8161172 < baseStart_8161172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161176 : List Nat := [2, 1, 2, 6, 2, 1, 1, 8]
def baseStart_8161176 : Nat := 118140960795 + 8161176 * 2 ^ 59
def prefixEnd_8161176 : Nat := 4983230072969 + 3 ^ 40 * 8161176 * 2
def baseEnd_8161176 : Nat := 155207629405106170187683

theorem tailTrace_8161176 : CollatzResearch.WordTrace tailWord_8161176 prefixEnd_8161176 155207629405106170187683 := by
  unfold tailWord_8161176
  simp only [CollatzResearch.WordTrace]
  refine ⟨148831271340730322369199691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198441695120973763158932921 148831271340730322369199691)
  ·
    refine ⟨223246907011095483553799537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148831271340730322369199691 223246907011095483553799537)
    ·
      refine ⟨167435180258321612665349653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223246907011095483553799537 167435180258321612665349653)
      ·
        refine ⟨7848524074608825593688265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167435180258321612665349653 7848524074608825593688265)
        ·
          refine ⟨5886393055956619195266199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7848524074608825593688265 5886393055956619195266199)
          ·
            refine ⟨8829589583934928792899299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886393055956619195266199 8829589583934928792899299)
            ·
              refine ⟨13244384375902393189348949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8829589583934928792899299 13244384375902393189348949)
              ·
                refine ⟨155207629405106170187683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13244384375902393189348949 155207629405106170187683)
                ·
                  rfl

theorem cell23_8161176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 8].length) (baseStart_8161176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161176 prefixEnd_8161176 := by exact prefixLift 8161176
  have htrace : WordTrace (prefixWord ++ tailWord_8161176) baseStart_8161176 baseEnd_8161176 := by
    simpa [prefixWord, tailWord_8161176, baseEnd_8161176] using wordTrace_append hprefix tailTrace_8161176
  have hstable : (prefixWord ++ tailWord_8161176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161176).length < 2 ^ (prefixWord ++ tailWord_8161176).sum := by decide
  have hdescent : baseEnd_8161176 < baseStart_8161176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161186 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_8161186 : Nat := 118140960795 + 8161186 * 2 ^ 59
def prefixEnd_8161186 : Nat := 4983230072969 + 3 ^ 40 * 8161186 * 2
def baseEnd_8161186 : Nat := 4190611128744411555942395

theorem tailTrace_8161186 : CollatzResearch.WordTrace tailWord_8161186 prefixEnd_8161186 4190611128744411555942395 := by
  unfold tailWord_8161186
  simp only [CollatzResearch.WordTrace]
  refine ⟨74415726852856104111565853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198441938274282944297508941 74415726852856104111565853)
  ·
    refine ⟨27905897569821039041837195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74415726852856104111565853 27905897569821039041837195)
    ·
      refine ⟨41858846354731558562755793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27905897569821039041837195 41858846354731558562755793)
      ·
        refine ⟨31394134766048668922066845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41858846354731558562755793 31394134766048668922066845)
        ·
          refine ⟨11772800537268250845775067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31394134766048668922066845 11772800537268250845775067)
          ·
            refine ⟨17659200805902376268662601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772800537268250845775067 17659200805902376268662601)
            ·
              refine ⟨13244400604426782201496951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17659200805902376268662601 13244400604426782201496951)
              ·
                refine ⟨19866600906640173302245427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13244400604426782201496951 19866600906640173302245427)
                ·
                  refine ⟨29799901359960259953368141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19866600906640173302245427 29799901359960259953368141)
                  ·
                    refine ⟨11174963009985097482513053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29799901359960259953368141 11174963009985097482513053)
                    ·
                      refine ⟨4190611128744411555942395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11174963009985097482513053 4190611128744411555942395)
                      ·
                        rfl

theorem cell23_8161186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_8161186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161186 prefixEnd_8161186 := by exact prefixLift 8161186
  have htrace : WordTrace (prefixWord ++ tailWord_8161186) baseStart_8161186 baseEnd_8161186 := by
    simpa [prefixWord, tailWord_8161186, baseEnd_8161186] using wordTrace_append hprefix tailTrace_8161186
  have hstable : (prefixWord ++ tailWord_8161186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161186).length < 2 ^ (prefixWord ++ tailWord_8161186).sum := by decide
  have hdescent : baseEnd_8161186 < baseStart_8161186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161209 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 1, 4, 2]
def baseStart_8161209 : Nat := 118140960795 + 8161209 * 2 ^ 59
def prefixEnd_8161209 : Nat := 4983230072969 + 3 ^ 40 * 8161209 * 2
def baseEnd_8161209 : Nat := 4190622938799464965954789

theorem tailTrace_8161209 : CollatzResearch.WordTrace tailWord_8161209 prefixEnd_8161209 4190622938799464965954789 := by
  unfold tailWord_8161209
  simp only [CollatzResearch.WordTrace]
  refine ⟨297663746290341091374350681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198442497526894060916233787 297663746290341091374350681)
  ·
    refine ⟨223247809717755818530763011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297663746290341091374350681 223247809717755818530763011)
    ·
      refine ⟨334871714576633727796144517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223247809717755818530763011 334871714576633727796144517)
      ·
        refine ⟨62788446483118823961777097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334871714576633727796144517 62788446483118823961777097)
        ·
          refine ⟨47091334862339117971332823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62788446483118823961777097 47091334862339117971332823)
          ·
            refine ⟨70637002293508676956999235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47091334862339117971332823 70637002293508676956999235)
            ·
              refine ⟨105955503440263015435498853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70637002293508676956999235 105955503440263015435498853)
              ·
                refine ⟨19866656895049315394156035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105955503440263015435498853 19866656895049315394156035)
                ·
                  refine ⟨29799985342573973091234053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19866656895049315394156035 29799985342573973091234053)
                  ·
                    refine ⟨5587497251732619954606385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29799985342573973091234053 5587497251732619954606385)
                    ·
                      refine ⟨4190622938799464965954789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587497251732619954606385 4190622938799464965954789)
                      ·
                        rfl

theorem cell23_8161209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_8161209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161209 prefixEnd_8161209 := by exact prefixLift 8161209
  have htrace : WordTrace (prefixWord ++ tailWord_8161209) baseStart_8161209 baseEnd_8161209 := by
    simpa [prefixWord, tailWord_8161209, baseEnd_8161209] using wordTrace_append hprefix tailTrace_8161209
  have hstable : (prefixWord ++ tailWord_8161209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161209).length < 2 ^ (prefixWord ++ tailWord_8161209).sum := by decide
  have hdescent : baseEnd_8161209 < baseStart_8161209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161213 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_8161213 : Nat := 118140960795 + 8161213 * 2 ^ 59
def prefixEnd_8161213 : Nat := 4983230072969 + 3 ^ 40 * 8161213 * 2
def baseEnd_8161213 : Nat := 4190624992722082950304771

theorem tailTrace_8161213 : CollatzResearch.WordTrace tailWord_8161213 prefixEnd_8161213 4190624992722082950304771 := by
  unfold tailWord_8161213
  simp only [CollatzResearch.WordTrace]
  refine ⟨297663892182326600057496293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198442594788217733371664195 297663892182326600057496293)
  ·
    refine ⟨55811979784186237510780555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297663892182326600057496293 55811979784186237510780555)
    ·
      refine ⟨83717969676279356266170833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55811979784186237510780555 83717969676279356266170833)
      ·
        refine ⟨62788477257209517199628125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83717969676279356266170833 62788477257209517199628125)
        ·
          refine ⟨23545678971453568949860547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62788477257209517199628125 23545678971453568949860547)
          ·
            refine ⟨35318518457180353424790821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23545678971453568949860547 35318518457180353424790821)
            ·
              refine ⟨6622222210721316267148279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35318518457180353424790821 6622222210721316267148279)
              ·
                refine ⟨9933333316081974400722419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622222210721316267148279 9933333316081974400722419)
                ·
                  refine ⟨14899999974122961601083629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9933333316081974400722419 14899999974122961601083629)
                  ·
                    refine ⟨5587499990296110600406361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14899999974122961601083629 5587499990296110600406361)
                    ·
                      refine ⟨4190624992722082950304771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587499990296110600406361 4190624992722082950304771)
                      ·
                        rfl

theorem cell23_8161213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_8161213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161213 prefixEnd_8161213 := by exact prefixLift 8161213
  have htrace : WordTrace (prefixWord ++ tailWord_8161213) baseStart_8161213 baseEnd_8161213 := by
    simpa [prefixWord, tailWord_8161213, baseEnd_8161213] using wordTrace_append hprefix tailTrace_8161213
  have hstable : (prefixWord ++ tailWord_8161213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161213).length < 2 ^ (prefixWord ++ tailWord_8161213).sum := by decide
  have hdescent : baseEnd_8161213 < baseStart_8161213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161215 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 9]
def baseStart_8161215 : Nat := 118140960795 + 8161215 * 2 ^ 59
def prefixEnd_8161215 : Nat := 4983230072969 + 3 ^ 40 * 8161215 * 2
def baseEnd_8161215 : Nat := 465625113298154660275529

theorem tailTrace_8161215 : CollatzResearch.WordTrace tailWord_8161215 prefixEnd_8161215 465625113298154660275529 := by
  unfold tailWord_8161215
  simp only [CollatzResearch.WordTrace]
  refine ⟨297663965128319354399069099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198442643418879569599379399 297663965128319354399069099)
  ·
    refine ⟨446495947692479031598603649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297663965128319354399069099 446495947692479031598603649)
    ·
      refine ⟨334871960769359273698952737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446495947692479031598603649 334871960769359273698952737)
      ·
        refine ⟨251153970577019455274214553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334871960769359273698952737 251153970577019455274214553)
        ·
          refine ⟨188365477932764591455660915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251153970577019455274214553 188365477932764591455660915)
          ·
            refine ⟨282548216899146887183491373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188365477932764591455660915 282548216899146887183491373)
            ·
              refine ⟨105955581337180082693809265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282548216899146887183491373 105955581337180082693809265)
              ·
                refine ⟨79466686002885062020356949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105955581337180082693809265 79466686002885062020356949)
                ·
                  refine ⟨465625113298154660275529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79466686002885062020356949 465625113298154660275529)
                  ·
                    rfl

theorem cell23_8161215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 9].length) (baseStart_8161215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161215 prefixEnd_8161215 := by exact prefixLift 8161215
  have htrace : WordTrace (prefixWord ++ tailWord_8161215) baseStart_8161215 baseEnd_8161215 := by
    simpa [prefixWord, tailWord_8161215, baseEnd_8161215] using wordTrace_append hprefix tailTrace_8161215
  have hstable : (prefixWord ++ tailWord_8161215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161215).length < 2 ^ (prefixWord ++ tailWord_8161215).sum := by decide
  have hdescent : baseEnd_8161215 < baseStart_8161215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161225 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_8161225 : Nat := 118140960795 + 8161225 * 2 ^ 59
def prefixEnd_8161225 : Nat := 4983230072969 + 3 ^ 40 * 8161225 * 2
def baseEnd_8161225 : Nat := 4190631154489936903354715

theorem tailTrace_8161225 : CollatzResearch.WordTrace tailWord_8161225 prefixEnd_8161225 4190631154489936903354715 := by
  unfold tailWord_8161225
  simp only [CollatzResearch.WordTrace]
  refine ⟨297664329858283126106933129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198442886572188750737955419 297664329858283126106933129)
  ·
    refine ⟨223248247393712344580199847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297664329858283126106933129 223248247393712344580199847)
    ·
      refine ⟨334872371090568516870299771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223248247393712344580199847 334872371090568516870299771)
      ·
        refine ⟨502308556635852775305449657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334872371090568516870299771 502308556635852775305449657)
        ·
          refine ⟨376731417476889581479087243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502308556635852775305449657 376731417476889581479087243)
          ·
            refine ⟨565097126215334372218630865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376731417476889581479087243 565097126215334372218630865)
            ·
              refine ⟨423822844661500779163973149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565097126215334372218630865 423822844661500779163973149)
              ·
                refine ⟨158933566748062792186489931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423822844661500779163973149 158933566748062792186489931)
                ·
                  refine ⟨238400350122094188279734897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158933566748062792186489931 238400350122094188279734897)
                  ·
                    refine ⟨178800262591570641209801173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238400350122094188279734897 178800262591570641209801173)
                    ·
                      refine ⟨4190631154489936903354715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178800262591570641209801173 4190631154489936903354715)
                      ·
                        rfl

theorem cell23_8161225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_8161225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161225 prefixEnd_8161225 := by exact prefixLift 8161225
  have htrace : WordTrace (prefixWord ++ tailWord_8161225) baseStart_8161225 baseEnd_8161225 := by
    simpa [prefixWord, tailWord_8161225, baseEnd_8161225] using wordTrace_append hprefix tailTrace_8161225
  have hstable : (prefixWord ++ tailWord_8161225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161225).length < 2 ^ (prefixWord ++ tailWord_8161225).sum := by decide
  have hdescent : baseEnd_8161225 < baseStart_8161225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161299 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 2, 4, 2]
def baseStart_8161299 : Nat := 118140960795 + 8161299 * 2 ^ 59
def prefixEnd_8161299 : Nat := 4983230072969 + 3 ^ 40 * 8161299 * 2
def baseEnd_8161299 : Nat := 4190669152058369613829375

theorem tailTrace_8161299 : CollatzResearch.WordTrace tailWord_8161299 prefixEnd_8161299 4190669152058369613829375 := by
  unfold tailWord_8161299
  simp only [CollatzResearch.WordTrace]
  refine ⟨297667028860015036745126951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198444685906676691163417967 297667028860015036745126951)
  ·
    refine ⟨446500543290022555117690427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297667028860015036745126951 446500543290022555117690427)
    ·
      refine ⟨669750814935033832676535641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446500543290022555117690427 669750814935033832676535641)
      ·
        refine ⟨502313111201275374507401731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669750814935033832676535641 502313111201275374507401731)
        ·
          refine ⟨753469666801913061761102597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502313111201275374507401731 753469666801913061761102597)
          ·
            refine ⟨141275562525358699080206737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 753469666801913061761102597 141275562525358699080206737)
            ·
              refine ⟨105956671894019024310155053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141275562525358699080206737 105956671894019024310155053)
              ·
                refine ⟨39733751960257134116308145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105956671894019024310155053 39733751960257134116308145)
                ·
                  refine ⟨29800313970192850587231109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39733751960257134116308145 29800313970192850587231109)
                  ·
                    refine ⟨5587558869411159485105833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29800313970192850587231109 5587558869411159485105833)
                    ·
                      refine ⟨4190669152058369613829375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587558869411159485105833 4190669152058369613829375)
                      ·
                        rfl

theorem cell23_8161299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4, 2].length) (baseStart_8161299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161299 prefixEnd_8161299 := by exact prefixLift 8161299
  have htrace : WordTrace (prefixWord ++ tailWord_8161299) baseStart_8161299 baseEnd_8161299 := by
    simpa [prefixWord, tailWord_8161299, baseEnd_8161299] using wordTrace_append hprefix tailTrace_8161299
  have hstable : (prefixWord ++ tailWord_8161299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161299).length < 2 ^ (prefixWord ++ tailWord_8161299).sum := by decide
  have hdescent : baseEnd_8161299 < baseStart_8161299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161343 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 1, 4]
def baseStart_8161343 : Nat := 118140960795 + 8161343 * 2 ^ 59
def prefixEnd_8161343 : Nat := 4983230072969 + 3 ^ 40 * 8161343 * 2
def baseEnd_8161343 : Nat := 1396897248402389147226391

theorem tailTrace_8161343 : CollatzResearch.WordTrace tailWord_8161343 prefixEnd_8161343 1396897248402389147226391 := by
  unfold tailWord_8161343
  simp only [CollatzResearch.WordTrace]
  refine ⟨297668633671855632259728683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198445755781237088173152455 297668633671855632259728683)
  ·
    refine ⟨446502950507783448389593025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297668633671855632259728683 446502950507783448389593025)
    ·
      refine ⟨334877212880837586292194769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446502950507783448389593025 334877212880837586292194769)
      ·
        refine ⟨251157909660628189719146077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334877212880837586292194769 251157909660628189719146077)
        ·
          refine ⟨94184216122735571144679779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251157909660628189719146077 94184216122735571144679779)
          ·
            refine ⟨141276324184103356717019669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94184216122735571144679779 141276324184103356717019669)
            ·
              refine ⟨6622327696129844846110297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141276324184103356717019669 6622327696129844846110297)
              ·
                refine ⟨4966745772097383634582723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622327696129844846110297 4966745772097383634582723)
                ·
                  refine ⟨7450118658146075451874085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966745772097383634582723 7450118658146075451874085)
                  ·
                    refine ⟨1396897248402389147226391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7450118658146075451874085 1396897248402389147226391)
                    ·
                      rfl

theorem cell23_8161343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 4].length) (baseStart_8161343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161343 prefixEnd_8161343 := by exact prefixLift 8161343
  have htrace : WordTrace (prefixWord ++ tailWord_8161343) baseStart_8161343 baseEnd_8161343 := by
    simpa [prefixWord, tailWord_8161343, baseEnd_8161343] using wordTrace_append hprefix tailTrace_8161343
  have hstable : (prefixWord ++ tailWord_8161343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161343).length < 2 ^ (prefixWord ++ tailWord_8161343).sum := by decide
  have hdescent : baseEnd_8161343 < baseStart_8161343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161359 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 3, 5, 2]
def baseStart_8161359 : Nat := 118140960795 + 8161359 * 2 ^ 59
def prefixEnd_8161359 : Nat := 4983230072969 + 3 ^ 40 * 8161359 * 2
def baseEnd_8161359 : Nat := 4190699960897639379079099

theorem tailTrace_8161359 : CollatzResearch.WordTrace tailWord_8161359 prefixEnd_8161359 4190699960897639379079099 := by
  unfold tailWord_8161359
  simp only [CollatzResearch.WordTrace]
  refine ⟨297669217239797666992311131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198446144826531777994874087 297669217239797666992311131)
  ·
    refine ⟨446503825859696500488466697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297669217239797666992311131 446503825859696500488466697)
    ·
      refine ⟨334877869394772375366350023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446503825859696500488466697 334877869394772375366350023)
      ·
        refine ⟨502316804092158563049525035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334877869394772375366350023 502316804092158563049525035)
        ·
          refine ⟨753475206138237844574287553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502316804092158563049525035 753475206138237844574287553)
          ·
            refine ⟨565106404603678383430715665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753475206138237844574287553 565106404603678383430715665)
            ·
              refine ⟨423829803452758787573036749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565106404603678383430715665 423829803452758787573036749)
              ·
                refine ⟨158936176294784545339888781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423829803452758787573036749 158936176294784545339888781)
                ·
                  refine ⟨59601066110544204502458293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158936176294784545339888781 59601066110544204502458293)
                  ·
                    refine ⟨5587599947863519172105465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59601066110544204502458293 5587599947863519172105465)
                    ·
                      refine ⟨4190699960897639379079099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587599947863519172105465 4190699960897639379079099)
                      ·
                        rfl

theorem cell23_8161359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5, 2].length) (baseStart_8161359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161359 prefixEnd_8161359 := by exact prefixLift 8161359
  have htrace : WordTrace (prefixWord ++ tailWord_8161359) baseStart_8161359 baseEnd_8161359 := by
    simpa [prefixWord, tailWord_8161359, baseEnd_8161359] using wordTrace_append hprefix tailTrace_8161359
  have hstable : (prefixWord ++ tailWord_8161359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161359).length < 2 ^ (prefixWord ++ tailWord_8161359).sum := by decide
  have hdescent : baseEnd_8161359 < baseStart_8161359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161369 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 1, 5]
def baseStart_8161369 : Nat := 118140960795 + 8161369 * 2 ^ 59
def prefixEnd_8161369 : Nat := 4983230072969 + 3 ^ 40 * 8161369 * 2
def baseEnd_8161369 : Nat := 1396901698568061446651351

theorem tailTrace_8161369 : CollatzResearch.WordTrace tailWord_8161369 prefixEnd_8161369 1396901698568061446651351 := by
  unfold tailWord_8161369
  simp only [CollatzResearch.WordTrace]
  refine ⟨297669581969761438700175161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198446387979840959133450107 297669581969761438700175161)
  ·
    refine ⟨223252186477321079025131371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297669581969761438700175161 223252186477321079025131371)
    ·
      refine ⟨334878279715981618537697057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223252186477321079025131371 334878279715981618537697057)
      ·
        refine ⟨251158709786986213903272793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334878279715981618537697057 251158709786986213903272793)
        ·
          refine ⟨188369032340239660427454595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251158709786986213903272793 188369032340239660427454595)
          ·
            refine ⟨282553548510359490641181893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188369032340239660427454595 282553548510359490641181893)
            ·
              refine ⟨52978790345692404495221605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282553548510359490641181893 52978790345692404495221605)
              ·
                refine ⟨9933523189817325842854051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52978790345692404495221605 9933523189817325842854051)
                ·
                  refine ⟨14900284784725988764281077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9933523189817325842854051 14900284784725988764281077)
                  ·
                    refine ⟨1396901698568061446651351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14900284784725988764281077 1396901698568061446651351)
                    ·
                      rfl

theorem cell23_8161369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_8161369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161369 prefixEnd_8161369 := by exact prefixLift 8161369
  have htrace : WordTrace (prefixWord ++ tailWord_8161369) baseStart_8161369 baseEnd_8161369 := by
    simpa [prefixWord, tailWord_8161369, baseEnd_8161369] using wordTrace_append hprefix tailTrace_8161369
  have hstable : (prefixWord ++ tailWord_8161369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161369).length < 2 ^ (prefixWord ++ tailWord_8161369).sum := by decide
  have hdescent : baseEnd_8161369 < baseStart_8161369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161376 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 1, 5, 2]
def baseStart_8161376 : Nat := 118140960795 + 8161376 * 2 ^ 59
def prefixEnd_8161376 : Nat := 4983230072969 + 3 ^ 40 * 8161376 * 2
def baseEnd_8161376 : Nat := 4190708690068765812566521

theorem tailTrace_8161376 : CollatzResearch.WordTrace tailWord_8161376 prefixEnd_8161376 4190708690068765812566521 := by
  unfold tailWord_8161376
  simp only [CollatzResearch.WordTrace]
  refine ⟨148834918640368039447839991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198446558187157385930453321 148834918640368039447839991)
  ·
    refine ⟨223252377960552059171759987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148834918640368039447839991 223252377960552059171759987)
    ·
      refine ⟨334878566940828088757639981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223252377960552059171759987 334878566940828088757639981)
      ·
        refine ⟨125579462602810533284114993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334878566940828088757639981 125579462602810533284114993)
        ·
          refine ⟨94184596952107899963086245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125579462602810533284114993 94184596952107899963086245)
          ·
            refine ⟨17659611928520231243078671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94184596952107899963086245 17659611928520231243078671)
            ·
              refine ⟨26489417892780346864618007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17659611928520231243078671 26489417892780346864618007)
              ·
                refine ⟨39734126839170520296927011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26489417892780346864618007 39734126839170520296927011)
                ·
                  refine ⟨59601190258755780445390517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39734126839170520296927011 59601190258755780445390517)
                  ·
                    refine ⟨5587611586758354416755361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59601190258755780445390517 5587611586758354416755361)
                    ·
                      refine ⟨4190708690068765812566521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587611586758354416755361 4190708690068765812566521)
                      ·
                        rfl

theorem cell23_8161376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_8161376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161376 prefixEnd_8161376 := by exact prefixLift 8161376
  have htrace : WordTrace (prefixWord ++ tailWord_8161376) baseStart_8161376 baseEnd_8161376 := by
    simpa [prefixWord, tailWord_8161376, baseEnd_8161376] using wordTrace_append hprefix tailTrace_8161376
  have hstable : (prefixWord ++ tailWord_8161376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161376).length < 2 ^ (prefixWord ++ tailWord_8161376).sum := by decide
  have hdescent : baseEnd_8161376 < baseStart_8161376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161416 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 1, 6]
def baseStart_8161416 : Nat := 118140960795 + 8161416 * 2 ^ 59
def prefixEnd_8161416 : Nat := 4983230072969 + 3 ^ 40 * 8161416 * 2
def baseEnd_8161416 : Nat := 1396909743098315218688779

theorem tailTrace_8161416 : CollatzResearch.WordTrace tailWord_8161416 prefixEnd_8161416 1396909743098315218688779 := by
  unfold tailWord_8161416
  simp only [CollatzResearch.WordTrace]
  refine ⟨148835648100295582863568051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198447530800394110484757401 148835648100295582863568051)
  ·
    refine ⟨223253472150443374295352077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148835648100295582863568051 223253472150443374295352077)
    ·
      refine ⟨83720052056416265360757029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223253472150443374295352077 83720052056416265360757029)
      ·
        refine ⟨15697509760578049755141943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83720052056416265360757029 15697509760578049755141943)
        ·
          refine ⟨23546264640867074632712915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15697509760578049755141943 23546264640867074632712915)
          ·
            refine ⟨35319396961300611949069373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23546264640867074632712915 35319396961300611949069373)
            ·
              refine ⟨13244773860487729480901015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35319396961300611949069373 13244773860487729480901015)
              ·
                refine ⟨19867160790731594221351523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13244773860487729480901015 19867160790731594221351523)
                ·
                  refine ⟨29800741186097391332027285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19867160790731594221351523 29800741186097391332027285)
                  ·
                    refine ⟨1396909743098315218688779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29800741186097391332027285 1396909743098315218688779)
                    ·
                      rfl

theorem cell23_8161416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_8161416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161416 prefixEnd_8161416 := by exact prefixLift 8161416
  have htrace : WordTrace (prefixWord ++ tailWord_8161416) baseStart_8161416 baseEnd_8161416 := by
    simpa [prefixWord, tailWord_8161416, baseEnd_8161416] using wordTrace_append hprefix tailTrace_8161416
  have hstable : (prefixWord ++ tailWord_8161416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161416).length < 2 ^ (prefixWord ++ tailWord_8161416).sum := by decide
  have hdescent : baseEnd_8161416 < baseStart_8161416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161434 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3]
def baseStart_8161434 : Nat := 118140960795 + 8161434 * 2 ^ 59
def prefixEnd_8161434 : Nat := 4983230072969 + 3 ^ 40 * 8161434 * 2
def baseEnd_8161434 : Nat := 4190738471946726585641255

theorem tailTrace_8161434 : CollatzResearch.WordTrace tailWord_8161434 prefixEnd_8161434 4190738471946726585641255 := by
  unfold tailWord_8161434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74417988178631488700322839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198447968476350636534194237 74417988178631488700322839)
  ·
    refine ⟨111626982267947233050484259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74417988178631488700322839 111626982267947233050484259)
    ·
      refine ⟨167440473401920849575726389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111626982267947233050484259 167440473401920849575726389)
      ·
        refine ⟨15697544381430079647724349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167440473401920849575726389 15697544381430079647724349)
        ·
          refine ⟨5886579143036279867896631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15697544381430079647724349 5886579143036279867896631)
          ·
            refine ⟨8829868714554419801844947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886579143036279867896631 8829868714554419801844947)
            ·
              refine ⟨13244803071831629702767421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8829868714554419801844947 13244803071831629702767421)
              ·
                refine ⟨4966801151936861138537783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13244803071831629702767421 4966801151936861138537783)
                ·
                  refine ⟨7450201727905291707806675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966801151936861138537783 7450201727905291707806675)
                  ·
                    refine ⟨11175302591857937561710013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7450201727905291707806675 11175302591857937561710013)
                    ·
                      refine ⟨4190738471946726585641255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11175302591857937561710013 4190738471946726585641255)
                      ·
                        rfl

theorem cell23_8161434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_8161434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161434 prefixEnd_8161434 := by exact prefixLift 8161434
  have htrace : WordTrace (prefixWord ++ tailWord_8161434) baseStart_8161434 baseEnd_8161434 := by
    simpa [prefixWord, tailWord_8161434, baseEnd_8161434] using wordTrace_append hprefix tailTrace_8161434
  have hstable : (prefixWord ++ tailWord_8161434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161434).length < 2 ^ (prefixWord ++ tailWord_8161434).sum := by decide
  have hdescent : baseEnd_8161434 < baseStart_8161434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161457 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 3, 2, 2]
def baseStart_8161457 : Nat := 118140960795 + 8161457 * 2 ^ 59
def prefixEnd_8161457 : Nat := 4983230072969 + 3 ^ 40 * 8161457 * 2
def baseEnd_8161457 : Nat := 4190750282001779995653649

theorem tailTrace_8161457 : CollatzResearch.WordTrace tailWord_8161457 prefixEnd_8161457 4190750282001779995653649 := by
  unfold tailWord_8161457
  simp only [CollatzResearch.WordTrace]
  refine ⟨297672791593442629729378625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198448527728961753152919083 297672791593442629729378625)
  ·
    refine ⟨223254593695081972297033969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297672791593442629729378625 223254593695081972297033969)
    ·
      refine ⟨167440945271311479222775477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223254593695081972297033969 167440945271311479222775477)
      ·
        refine ⟨15697588619185451177135201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167440945271311479222775477 15697588619185451177135201)
        ·
          refine ⟨11773191464389088382851401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15697588619185451177135201 11773191464389088382851401)
          ·
            refine ⟨8829893598291816287138551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773191464389088382851401 8829893598291816287138551)
            ·
              refine ⟨13244840397437724430707827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8829893598291816287138551 13244840397437724430707827)
              ·
                refine ⟨19867260596156586646061741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13244840397437724430707827 19867260596156586646061741)
                ·
                  refine ⟨7450222723558719992273153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19867260596156586646061741 7450222723558719992273153)
                  ·
                    refine ⟨5587667042669039994204865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7450222723558719992273153 5587667042669039994204865)
                    ·
                      refine ⟨4190750282001779995653649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587667042669039994204865 4190750282001779995653649)
                      ·
                        rfl

theorem cell23_8161457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_8161457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161457 prefixEnd_8161457 := by exact prefixLift 8161457
  have htrace : WordTrace (prefixWord ++ tailWord_8161457) baseStart_8161457 baseEnd_8161457 := by
    simpa [prefixWord, tailWord_8161457, baseEnd_8161457] using wordTrace_append hprefix tailTrace_8161457
  have hstable : (prefixWord ++ tailWord_8161457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161457).length < 2 ^ (prefixWord ++ tailWord_8161457).sum := by decide
  have hdescent : baseEnd_8161457 < baseStart_8161457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3]
def baseStart_8161499 : Nat := 118140960795 + 8161499 * 2 ^ 59
def prefixEnd_8161499 : Nat := 4983230072969 + 3 ^ 40 * 8161499 * 2
def baseEnd_8161499 : Nat := 4190771848189268831328455

theorem tailTrace_8161499 : CollatzResearch.WordTrace tailWord_8161499 prefixEnd_8161499 4190771848189268831328455 := by
  unfold tailWord_8161499
  simp only [CollatzResearch.WordTrace]
  refine ⟨297674323459290470902407551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198449548972860313934938367 297674323459290470902407551)
  ·
    refine ⟨446511485188935706353611327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297674323459290470902407551 446511485188935706353611327)
    ·
      refine ⟨669767227783403559530416991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446511485188935706353611327 669767227783403559530416991)
      ·
        refine ⟨1004650841675105339295625487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669767227783403559530416991 1004650841675105339295625487)
        ·
          refine ⟨1506976262512658008943438231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004650841675105339295625487 1506976262512658008943438231)
          ·
            refine ⟨2260464393768987013415157347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506976262512658008943438231 2260464393768987013415157347)
            ·
              refine ⟨3390696590653480520122736021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260464393768987013415157347 3390696590653480520122736021)
              ·
                refine ⟨158938902686881899380753251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3390696590653480520122736021 158938902686881899380753251)
                ·
                  refine ⟨238408354030322849071129877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158938902686881899380753251 238408354030322849071129877)
                  ·
                    refine ⟨11175391595171383550209213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 238408354030322849071129877 11175391595171383550209213)
                    ·
                      refine ⟨4190771848189268831328455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11175391595171383550209213 4190771848189268831328455)
                      ·
                        rfl

theorem cell23_8161499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3].length) (baseStart_8161499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161499 prefixEnd_8161499 := by exact prefixLift 8161499
  have htrace : WordTrace (prefixWord ++ tailWord_8161499) baseStart_8161499 baseEnd_8161499 := by
    simpa [prefixWord, tailWord_8161499, baseEnd_8161499] using wordTrace_append hprefix tailTrace_8161499
  have hstable : (prefixWord ++ tailWord_8161499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161499).length < 2 ^ (prefixWord ++ tailWord_8161499).sum := by decide
  have hdescent : baseEnd_8161499 < baseStart_8161499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161507 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8161507 : Nat := 118140960795 + 8161507 * 2 ^ 59
def prefixEnd_8161507 : Nat := 4983230072969 + 3 ^ 40 * 8161507 * 2
def baseEnd_8161507 : Nat := 4190775956034504800028419

theorem tailTrace_8161507 : CollatzResearch.WordTrace tailWord_8161507 prefixEnd_8161507 4190775956034504800028419 := by
  unfold tailWord_8161507
  simp only [CollatzResearch.WordTrace]
  refine ⟨297674615243261488268698775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198449743495507658845799183 297674615243261488268698775)
  ·
    refine ⟨446511922864892232403048163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297674615243261488268698775 446511922864892232403048163)
    ·
      refine ⟨669767884297338348604572245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446511922864892232403048163 669767884297338348604572245)
      ·
        refine ⟨7848842394109433772709831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 669767884297338348604572245 7848842394109433772709831)
        ·
          refine ⟨11773263591164150659064747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848842394109433772709831 11773263591164150659064747)
          ·
            refine ⟨17659895386746225988597121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773263591164150659064747 17659895386746225988597121)
            ·
              refine ⟨13244921540059669491447841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17659895386746225988597121 13244921540059669491447841)
              ·
                refine ⟨9933691155044752118585881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13244921540059669491447841 9933691155044752118585881)
                ·
                  refine ⟨7450268366283564088939411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9933691155044752118585881 7450268366283564088939411)
                  ·
                    refine ⟨11175402549425346133409117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7450268366283564088939411 11175402549425346133409117)
                    ·
                      refine ⟨4190775956034504800028419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11175402549425346133409117 4190775956034504800028419)
                      ·
                        rfl

theorem cell23_8161507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8161507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161507 prefixEnd_8161507 := by exact prefixLift 8161507
  have htrace : WordTrace (prefixWord ++ tailWord_8161507) baseStart_8161507 baseEnd_8161507 := by
    simpa [prefixWord, tailWord_8161507, baseEnd_8161507] using wordTrace_append hprefix tailTrace_8161507
  have hstable : (prefixWord ++ tailWord_8161507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161507).length < 2 ^ (prefixWord ++ tailWord_8161507).sum := by decide
  have hdescent : baseEnd_8161507 < baseStart_8161507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161526 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_8161526 : Nat := 118140960795 + 8161526 * 2 ^ 59
def prefixEnd_8161526 : Nat := 4983230072969 + 3 ^ 40 * 8161526 * 2
def baseEnd_8161526 : Nat := 4190785712166940225690831

theorem tailTrace_8161526 : CollatzResearch.WordTrace tailWord_8161526 prefixEnd_8161526 4190785712166940225690831 := by
  unfold tailWord_8161526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604706764387040907102527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198450205486795103009093621 18604706764387040907102527)
  ·
    refine ⟨27907060146580561360653791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18604706764387040907102527 27907060146580561360653791)
    ·
      refine ⟨41860590219870842040980687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27907060146580561360653791 41860590219870842040980687)
      ·
        refine ⟨62790885329806263061471031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41860590219870842040980687 62790885329806263061471031)
        ·
          refine ⟨94186327994709394592206547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62790885329806263061471031 94186327994709394592206547)
          ·
            refine ⟨141279491992064091888309821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94186327994709394592206547 141279491992064091888309821)
            ·
              refine ⟨52979809497024034458116183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141279491992064091888309821 52979809497024034458116183)
              ·
                refine ⟨79469714245536051687174275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52979809497024034458116183 79469714245536051687174275)
                ·
                  refine ⟨119204571368304077530761413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79469714245536051687174275 119204571368304077530761413)
                  ·
                    refine ⟨22350857131557014537017765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119204571368304077530761413 22350857131557014537017765)
                    ·
                      refine ⟨4190785712166940225690831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22350857131557014537017765 4190785712166940225690831)
                      ·
                        rfl

theorem cell23_8161526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_8161526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161526 prefixEnd_8161526 := by exact prefixLift 8161526
  have htrace : WordTrace (prefixWord ++ tailWord_8161526) baseStart_8161526 baseEnd_8161526 := by
    simpa [prefixWord, tailWord_8161526, baseEnd_8161526] using wordTrace_append hprefix tailTrace_8161526
  have hstable : (prefixWord ++ tailWord_8161526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161526).length < 2 ^ (prefixWord ++ tailWord_8161526).sum := by decide
  have hdescent : baseEnd_8161526 < baseStart_8161526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161530 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2]
def baseStart_8161530 : Nat := 118140960795 + 8161530 * 2 ^ 59
def prefixEnd_8161530 : Nat := 4983230072969 + 3 ^ 40 * 8161530 * 2
def baseEnd_8161530 : Nat := 4190787766089558210040813

theorem tailTrace_8161530 : CollatzResearch.WordTrace tailWord_8161530 prefixEnd_8161530 4190787766089558210040813 := by
  unfold tailWord_8161530
  simp only [CollatzResearch.WordTrace]
  refine ⟨74418863530544540799196511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198450302748118775464524029 74418863530544540799196511)
  ·
    refine ⟨111628295295816811198794767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74418863530544540799196511 111628295295816811198794767)
    ·
      refine ⟨167442442943725216798192151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111628295295816811198794767 167442442943725216798192151)
      ·
        refine ⟨251163664415587825197288227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167442442943725216798192151 251163664415587825197288227)
        ·
          refine ⟨376745496623381737795932341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251163664415587825197288227 376745496623381737795932341)
          ·
            refine ⟨35319890308442037918368657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376745496623381737795932341 35319890308442037918368657)
            ·
              refine ⟨26489917731331528438776493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35319890308442037918368657 26489917731331528438776493)
              ·
                refine ⟨9933719149249323164541185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26489917731331528438776493 9933719149249323164541185)
                ·
                  refine ⟨7450289361936992373405889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9933719149249323164541185 7450289361936992373405889)
                  ·
                    refine ⟨5587717021452744280054417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7450289361936992373405889 5587717021452744280054417)
                    ·
                      refine ⟨4190787766089558210040813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587717021452744280054417 4190787766089558210040813)
                      ·
                        rfl

theorem cell23_8161530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_8161530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161530 prefixEnd_8161530 := by exact prefixLift 8161530
  have htrace : WordTrace (prefixWord ++ tailWord_8161530) baseStart_8161530 baseEnd_8161530 := by
    simpa [prefixWord, tailWord_8161530, baseEnd_8161530] using wordTrace_append hprefix tailTrace_8161530
  have hstable : (prefixWord ++ tailWord_8161530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161530).length < 2 ^ (prefixWord ++ tailWord_8161530).sum := by decide
  have hdescent : baseEnd_8161530 < baseStart_8161530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161553 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 5]
def baseStart_8161553 : Nat := 118140960795 + 8161553 * 2 ^ 59
def prefixEnd_8161553 : Nat := 4983230072969 + 3 ^ 40 * 8161553 * 2
def baseEnd_8161553 : Nat := 465644397349401291117023

theorem tailTrace_8161553 : CollatzResearch.WordTrace tailWord_8161553 prefixEnd_8161553 465644397349401291117023 := by
  unfold tailWord_8161553
  simp only [CollatzResearch.WordTrace]
  refine ⟨297676293001094838124873313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198450862000729892083248875 297676293001094838124873313)
  ·
    refine ⟨223257219750821128593654985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297676293001094838124873313 223257219750821128593654985)
    ·
      refine ⟨167442914813115846445241239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223257219750821128593654985 167442914813115846445241239)
      ·
        refine ⟨251164372219673769667861859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167442914813115846445241239 251164372219673769667861859)
        ·
          refine ⟨376746558329510654501792789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251164372219673769667861859 376746558329510654501792789)
          ·
            refine ⟨17659994921695811929771537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 376746558329510654501792789 17659994921695811929771537)
            ·
              refine ⟨13244996191271858947328653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17659994921695811929771537 13244996191271858947328653)
              ·
                refine ⟨4966873571726947105248245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13244996191271858947328653 4966873571726947105248245)
                ·
                  refine ⟨465644397349401291117023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4966873571726947105248245 465644397349401291117023)
                  ·
                    rfl

theorem cell23_8161553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 5].length) (baseStart_8161553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161553 prefixEnd_8161553 := by exact prefixLift 8161553
  have htrace : WordTrace (prefixWord ++ tailWord_8161553) baseStart_8161553 baseEnd_8161553 := by
    simpa [prefixWord, tailWord_8161553, baseEnd_8161553] using wordTrace_append hprefix tailTrace_8161553
  have hstable : (prefixWord ++ tailWord_8161553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161553).length < 2 ^ (prefixWord ++ tailWord_8161553).sum := by decide
  have hdescent : baseEnd_8161553 < baseStart_8161553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161581 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_8161581 : Nat := 118140960795 + 8161581 * 2 ^ 59
def prefixEnd_8161581 : Nat := 4983230072969 + 3 ^ 40 * 8161581 * 2
def baseEnd_8161581 : Nat := 4190813953602937510503079

theorem tailTrace_8161581 : CollatzResearch.WordTrace tailWord_8161581 prefixEnd_8161581 4190813953602937510503079 := by
  unfold tailWord_8161581
  simp only [CollatzResearch.WordTrace]
  refine ⟨297677314244993398906892597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198451542829995599271261731 297677314244993398906892597)
  ·
    refine ⟨27907248210468131147521181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297677314244993398906892597 27907248210468131147521181)
    ·
      refine ⟨10465218078925549180320443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27907248210468131147521181 10465218078925549180320443)
      ·
        refine ⟨15697827118388323770480665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10465218078925549180320443 15697827118388323770480665)
        ·
          refine ⟨11773370338791242827860499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15697827118388323770480665 11773370338791242827860499)
          ·
            refine ⟨17660055508186864241790749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773370338791242827860499 17660055508186864241790749)
            ·
              refine ⟨6622520815570074090671531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17660055508186864241790749 6622520815570074090671531)
              ·
                refine ⟨9933781223355111136007297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622520815570074090671531 9933781223355111136007297)
                ·
                  refine ⟨7450335917516333352005473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9933781223355111136007297 7450335917516333352005473)
                  ·
                    refine ⟨5587751938137250014004105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7450335917516333352005473 5587751938137250014004105)
                    ·
                      refine ⟨4190813953602937510503079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587751938137250014004105 4190813953602937510503079)
                      ·
                        rfl

theorem cell23_8161581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_8161581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161581 prefixEnd_8161581 := by exact prefixLift 8161581
  have htrace : WordTrace (prefixWord ++ tailWord_8161581) baseStart_8161581 baseEnd_8161581 := by
    simpa [prefixWord, tailWord_8161581, baseEnd_8161581] using wordTrace_append hprefix tailTrace_8161581
  have hstable : (prefixWord ++ tailWord_8161581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161581).length < 2 ^ (prefixWord ++ tailWord_8161581).sum := by decide
  have hdescent : baseEnd_8161581 < baseStart_8161581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161604 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 5]
def baseStart_8161604 : Nat := 118140960795 + 8161604 * 2 ^ 59
def prefixEnd_8161604 : Nat := 4983230072969 + 3 ^ 40 * 8161604 * 2
def baseEnd_8161604 : Nat := 465647307073110102279497

theorem tailTrace_8161604 : CollatzResearch.WordTrace tailWord_8161604 prefixEnd_8161604 465647307073110102279497 := by
  unfold tailWord_8161604
  simp only [CollatzResearch.WordTrace]
  refine ⟨148839076561955036917489933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198452102082606715889986577 148839076561955036917489933)
  ·
    refine ⟨55814653710733138844058725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148839076561955036917489933 55814653710733138844058725)
    ·
      refine ⟨10465247570762463533261011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55814653710733138844058725 10465247570762463533261011)
      ·
        refine ⟨15697871356143695299891517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10465247570762463533261011 15697871356143695299891517)
        ·
          refine ⟨5886701758553885737459319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15697871356143695299891517 5886701758553885737459319)
          ·
            refine ⟨8830052637830828606188979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886701758553885737459319 8830052637830828606188979)
            ·
              refine ⟨13245078956746242909283469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8830052637830828606188979 13245078956746242909283469)
              ·
                refine ⟨4966904608779841090981301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13245078956746242909283469 4966904608779841090981301)
                ·
                  refine ⟨465647307073110102279497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4966904608779841090981301 465647307073110102279497)
                  ·
                    rfl

theorem cell23_8161604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_8161604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161604 prefixEnd_8161604 := by exact prefixLift 8161604
  have htrace : WordTrace (prefixWord ++ tailWord_8161604) baseStart_8161604 baseEnd_8161604 := by
    simpa [prefixWord, tailWord_8161604, baseEnd_8161604] using wordTrace_append hprefix tailTrace_8161604
  have hstable : (prefixWord ++ tailWord_8161604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161604).length < 2 ^ (prefixWord ++ tailWord_8161604).sum := by decide
  have hdescent : baseEnd_8161604 < baseStart_8161604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161623 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_8161623 : Nat := 118140960795 + 8161623 * 2 ^ 59
def prefixEnd_8161623 : Nat := 4983230072969 + 3 ^ 40 * 8161623 * 2
def baseEnd_8161623 : Nat := 4190835519790426346177885

theorem tailTrace_8161623 : CollatzResearch.WordTrace tailWord_8161623 prefixEnd_8161623 4190835519790426346177885 := by
  unfold tailWord_8161623
  simp only [CollatzResearch.WordTrace]
  refine ⟨297678846110841240079921523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198452564073894160053281015 297678846110841240079921523)
  ·
    refine ⟨446518269166261860119882285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297678846110841240079921523 446518269166261860119882285)
    ·
      refine ⟨167444350937348197544955857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446518269166261860119882285 167444350937348197544955857)
      ·
        refine ⟨125583263203011148158716893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167444350937348197544955857 125583263203011148158716893)
        ·
          refine ⟨47093723701129180559518835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125583263203011148158716893 47093723701129180559518835)
          ·
            refine ⟨70640585551693770839278253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47093723701129180559518835 70640585551693770839278253)
            ·
              refine ⟨26490219581885164064729345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70640585551693770839278253 26490219581885164064729345)
              ·
                refine ⟨19867664686413873048547009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26490219581885164064729345 19867664686413873048547009)
                ·
                  refine ⟨14900748514810404786410257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19867664686413873048547009 14900748514810404786410257)
                  ·
                    refine ⟨11175561386107803589807693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14900748514810404786410257 11175561386107803589807693)
                    ·
                      refine ⟨4190835519790426346177885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11175561386107803589807693 4190835519790426346177885)
                      ·
                        rfl

theorem cell23_8161623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_8161623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161623 prefixEnd_8161623 := by exact prefixLift 8161623
  have htrace : WordTrace (prefixWord ++ tailWord_8161623) baseStart_8161623 baseEnd_8161623 := by
    simpa [prefixWord, tailWord_8161623, baseEnd_8161623] using wordTrace_append hprefix tailTrace_8161623
  have hstable : (prefixWord ++ tailWord_8161623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161623).length < 2 ^ (prefixWord ++ tailWord_8161623).sum := by decide
  have hdescent : baseEnd_8161623 < baseStart_8161623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161626 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_8161626 : Nat := 118140960795 + 8161626 * 2 ^ 59
def prefixEnd_8161626 : Nat := 4983230072969 + 3 ^ 40 * 8161626 * 2
def baseEnd_8161626 : Nat := 465648562248043314937819

theorem tailTrace_8161626 : CollatzResearch.WordTrace tailWord_8161626 prefixEnd_8161626 465648562248043314937819 := by
  unfold tailWord_8161626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74419738882457592898070183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198452637019886914394853821 74419738882457592898070183)
  ·
    refine ⟨111629608323686389347105275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74419738882457592898070183 111629608323686389347105275)
    ·
      refine ⟨167444412485529584020657913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111629608323686389347105275 167444412485529584020657913)
      ·
        refine ⟨125583309364147188015493435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167444412485529584020657913 125583309364147188015493435)
        ·
          refine ⟨188374964046220782023240153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125583309364147188015493435 188374964046220782023240153)
          ·
            refine ⟨141281223034665586517430115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188374964046220782023240153 141281223034665586517430115)
            ·
              refine ⟨211921834551998379776145173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141281223034665586517430115 211921834551998379776145173)
              ·
                refine ⟨9933835994624924052006805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211921834551998379776145173 9933835994624924052006805)
                ·
                  refine ⟨465648562248043314937819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9933835994624924052006805 465648562248043314937819)
                  ·
                    rfl

theorem cell23_8161626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_8161626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161626 prefixEnd_8161626 := by exact prefixLift 8161626
  have htrace : WordTrace (prefixWord ++ tailWord_8161626) baseStart_8161626 baseEnd_8161626 := by
    simpa [prefixWord, tailWord_8161626, baseEnd_8161626] using wordTrace_append hprefix tailTrace_8161626
  have hstable : (prefixWord ++ tailWord_8161626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161626).length < 2 ^ (prefixWord ++ tailWord_8161626).sum := by decide
  have hdescent : baseEnd_8161626 < baseStart_8161626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161663 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 6, 3, 2]
def baseStart_8161663 : Nat := 118140960795 + 8161663 * 2 ^ 59
def prefixEnd_8161663 : Nat := 4983230072969 + 3 ^ 40 * 8161663 * 2
def baseEnd_8161663 : Nat := 4190856059016606189677701

theorem tailTrace_8161663 : CollatzResearch.WordTrace tailWord_8161663 prefixEnd_8161663 4190856059016606189677701 := by
  unfold tailWord_8161663
  simp only [CollatzResearch.WordTrace]
  refine ⟨297680305030696326911377643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198453536687130884607585095 297680305030696326911377643)
  ·
    refine ⟨446520457546044490367066465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297680305030696326911377643 446520457546044490367066465)
    ·
      refine ⟨334890343159533367775299849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446520457546044490367066465 334890343159533367775299849)
      ·
        refine ⟨251167757369650025831474887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334890343159533367775299849 251167757369650025831474887)
        ·
          refine ⟨376751636054475038747212331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251167757369650025831474887 376751636054475038747212331)
          ·
            refine ⟨565127454081712558120818497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376751636054475038747212331 565127454081712558120818497)
            ·
              refine ⟨423845590561284418590613873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565127454081712558120818497 423845590561284418590613873)
              ·
                refine ⟨317884192920963313942960405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423845590561284418590613873 317884192920963313942960405)
                ·
                  refine ⟨14900821543170155341076269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317884192920963313942960405 14900821543170155341076269)
                  ·
                    refine ⟨5587808078688808252903601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14900821543170155341076269 5587808078688808252903601)
                    ·
                      refine ⟨4190856059016606189677701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587808078688808252903601 4190856059016606189677701)
                      ·
                        rfl

theorem cell23_8161663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_8161663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161663 prefixEnd_8161663 := by exact prefixLift 8161663
  have htrace : WordTrace (prefixWord ++ tailWord_8161663) baseStart_8161663 baseEnd_8161663 := by
    simpa [prefixWord, tailWord_8161663, baseEnd_8161663] using wordTrace_append hprefix tailTrace_8161663
  have hstable : (prefixWord ++ tailWord_8161663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161663).length < 2 ^ (prefixWord ++ tailWord_8161663).sum := by decide
  have hdescent : baseEnd_8161663 < baseStart_8161663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161703 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 1, 6]
def baseStart_8161703 : Nat := 118140960795 + 8161703 * 2 ^ 59
def prefixEnd_8161703 : Nat := 4983230072969 + 3 ^ 40 * 8161703 * 2
def baseEnd_8161703 : Nat := 1396958866080928677725839

theorem tailTrace_8161703 : CollatzResearch.WordTrace tailWord_8161703 prefixEnd_8161703 1396958866080928677725839 := by
  unfold tailWord_8161703
  simp only [CollatzResearch.WordTrace]
  refine ⟨297681763950551413742833763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198454509300367609161889175 297681763950551413742833763)
  ·
    refine ⟨446522645925827120614250645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297681763950551413742833763 446522645925827120614250645)
    ·
      refine ⟨20930749027773146278792999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 446522645925827120614250645 20930749027773146278792999)
      ·
        refine ⟨31396123541659719418189499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20930749027773146278792999 31396123541659719418189499)
        ·
          refine ⟨47094185312489579127284249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31396123541659719418189499 47094185312489579127284249)
          ·
            refine ⟨35320638984367184345463187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47094185312489579127284249 35320638984367184345463187)
            ·
              refine ⟨52980958476550776518194781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35320638984367184345463187 52980958476550776518194781)
              ·
                refine ⟨19867859428706541194323043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52980958476550776518194781 19867859428706541194323043)
                ·
                  refine ⟨29801789143059811791484565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19867859428706541194323043 29801789143059811791484565)
                  ·
                    refine ⟨1396958866080928677725839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29801789143059811791484565 1396958866080928677725839)
                    ·
                      rfl

theorem cell23_8161703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_8161703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161703 prefixEnd_8161703 := by exact prefixLift 8161703
  have htrace : WordTrace (prefixWord ++ tailWord_8161703) baseStart_8161703 baseEnd_8161703 := by
    simpa [prefixWord, tailWord_8161703, baseEnd_8161703] using wordTrace_append hprefix tailTrace_8161703
  have hstable : (prefixWord ++ tailWord_8161703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161703).length < 2 ^ (prefixWord ++ tailWord_8161703).sum := by decide
  have hdescent : baseEnd_8161703 < baseStart_8161703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161778 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_8161778 : Nat := 118140960795 + 8161778 * 2 ^ 59
def prefixEnd_8161778 : Nat := 4983230072969 + 3 ^ 40 * 8161778 * 2
def baseEnd_8161778 : Nat := 4190915109291873239739673

theorem tailTrace_8161778 : CollatzResearch.WordTrace tailWord_8161778 prefixEnd_8161778 4190915109291873239739673 := by
  unfold tailWord_8161778
  simp only [CollatzResearch.WordTrace]
  refine ⟨74421124856319925387953497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198456332950186467701209325 74421124856319925387953497)
  ·
    refine ⟨55815843642239944040965123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74421124856319925387953497 55815843642239944040965123)
    ·
      refine ⟨83723765463359916061447685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55815843642239944040965123 83723765463359916061447685)
      ·
        refine ⟨15698206024379984261521441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83723765463359916061447685 15698206024379984261521441)
        ·
          refine ⟨11773654518284988196141081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15698206024379984261521441 11773654518284988196141081)
          ·
            refine ⟨8830240888713741147105811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773654518284988196141081 8830240888713741147105811)
            ·
              refine ⟨13245361333070611720658717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8830240888713741147105811 13245361333070611720658717)
              ·
                refine ⟨4967010499901479395247019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13245361333070611720658717 4967010499901479395247019)
                ·
                  refine ⟨7450515749852219092870529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967010499901479395247019 7450515749852219092870529)
                  ·
                    refine ⟨5587886812389164319652897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7450515749852219092870529 5587886812389164319652897)
                    ·
                      refine ⟨4190915109291873239739673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587886812389164319652897 4190915109291873239739673)
                      ·
                        rfl

theorem cell23_8161778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_8161778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161778 prefixEnd_8161778 := by exact prefixLift 8161778
  have htrace : WordTrace (prefixWord ++ tailWord_8161778) baseStart_8161778 baseEnd_8161778 := by
    simpa [prefixWord, tailWord_8161778, baseEnd_8161778] using wordTrace_append hprefix tailTrace_8161778
  have hstable : (prefixWord ++ tailWord_8161778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161778).length < 2 ^ (prefixWord ++ tailWord_8161778).sum := by decide
  have hdescent : baseEnd_8161778 < baseStart_8161778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161813 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_8161813 : Nat := 118140960795 + 8161813 * 2 ^ 59
def prefixEnd_8161813 : Nat := 4983230072969 + 3 ^ 40 * 8161813 * 2
def baseEnd_8161813 : Nat := 4190933081114780602802011

theorem tailTrace_8161813 : CollatzResearch.WordTrace tailWord_8161813 prefixEnd_8161813 4190933081114780602802011 := by
  unfold tailWord_8161813
  simp only [CollatzResearch.WordTrace]
  refine ⟨297685775980152902529338093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198457183986768601686225395 297685775980152902529338093)
  ·
    refine ⟨111632165992557338448501785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297685775980152902529338093 111632165992557338448501785)
    ·
      refine ⟨83724124494418003836376339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111632165992557338448501785 83724124494418003836376339)
      ·
        refine ⟨125586186741627005754564509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83724124494418003836376339 125586186741627005754564509)
        ·
          refine ⟨47094820028110127157961691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125586186741627005754564509 47094820028110127157961691)
          ·
            refine ⟨70642230042165190736942537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47094820028110127157961691 70642230042165190736942537)
            ·
              refine ⟨52981672531623893052706903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70642230042165190736942537 52981672531623893052706903)
              ·
                refine ⟨79472508797435839579060355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52981672531623893052706903 79472508797435839579060355)
                ·
                  refine ⟨119208763196153759368590533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79472508797435839579060355 119208763196153759368590533)
                  ·
                    refine ⟨22351643099278829881610725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119208763196153759368590533 22351643099278829881610725)
                    ·
                      refine ⟨4190933081114780602802011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22351643099278829881610725 4190933081114780602802011)
                      ·
                        rfl

theorem cell23_8161813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_8161813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161813 prefixEnd_8161813 := by exact prefixLift 8161813
  have htrace : WordTrace (prefixWord ++ tailWord_8161813) baseStart_8161813 baseEnd_8161813 := by
    simpa [prefixWord, tailWord_8161813, baseEnd_8161813] using wordTrace_append hprefix tailTrace_8161813
  have hstable : (prefixWord ++ tailWord_8161813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161813).length < 2 ^ (prefixWord ++ tailWord_8161813).sum := by decide
  have hdescent : baseEnd_8161813 < baseStart_8161813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161817 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 2, 2, 2]
def baseStart_8161817 : Nat := 118140960795 + 8161817 * 2 ^ 59
def prefixEnd_8161817 : Nat := 4983230072969 + 3 ^ 40 * 8161817 * 2
def baseEnd_8161817 : Nat := 4190935135037398587151993

theorem tailTrace_8161817 : CollatzResearch.WordTrace tailWord_8161817 prefixEnd_8161817 4190935135037398587151993 := by
  unfold tailWord_8161817
  simp only [CollatzResearch.WordTrace]
  refine ⟨297685921872138411212483705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198457281248092274141655803 297685921872138411212483705)
  ·
    refine ⟨223264441404103808409362779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297685921872138411212483705 223264441404103808409362779)
    ·
      refine ⟨334896662106155712614044169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223264441404103808409362779 334896662106155712614044169)
      ·
        refine ⟨251172496579616784460533127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334896662106155712614044169 251172496579616784460533127)
        ·
          refine ⟨376758744869425176690799691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251172496579616784460533127 376758744869425176690799691)
          ·
            refine ⟨565138117304137765036199537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376758744869425176690799691 565138117304137765036199537)
            ·
              refine ⟨423853587978103323777149653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565138117304137765036199537 423853587978103323777149653)
              ·
                refine ⟨9934068468236796651026945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 423853587978103323777149653 9934068468236796651026945)
                ·
                  refine ⟨7450551351177597488270209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9934068468236796651026945 7450551351177597488270209)
                  ·
                    refine ⟨5587913513383198116202657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7450551351177597488270209 5587913513383198116202657)
                    ·
                      refine ⟨4190935135037398587151993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5587913513383198116202657 4190935135037398587151993)
                      ·
                        rfl

theorem cell23_8161817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_8161817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161817 prefixEnd_8161817 := by exact prefixLift 8161817
  have htrace : WordTrace (prefixWord ++ tailWord_8161817) baseStart_8161817 baseEnd_8161817 := by
    simpa [prefixWord, tailWord_8161817, baseEnd_8161817] using wordTrace_append hprefix tailTrace_8161817
  have hstable : (prefixWord ++ tailWord_8161817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161817).length < 2 ^ (prefixWord ++ tailWord_8161817).sum := by decide
  have hdescent : baseEnd_8161817 < baseStart_8161817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161857 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 5]
def baseStart_8161857 : Nat := 118140960795 + 8161857 * 2 ^ 59
def prefixEnd_8161857 : Nat := 4983230072969 + 3 ^ 40 * 8161857 * 2
def baseEnd_8161857 : Nat := 465661741584842047850201

theorem tailTrace_8161857 : CollatzResearch.WordTrace tailWord_8161857 prefixEnd_8161857 465661741584842047850201 := by
  unfold tailWord_8161857
  simp only [CollatzResearch.WordTrace]
  refine ⟨297687380791993498043939825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198458253861328998695959883 297687380791993498043939825)
  ·
    refine ⟨223265535593995123532954869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297687380791993498043939825 223265535593995123532954869)
    ·
      refine ⟨20931143961937042831214519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223265535593995123532954869 20931143961937042831214519)
      ·
        refine ⟨31396715942905564246821779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20931143961937042831214519 31396715942905564246821779)
        ·
          refine ⟨47095073914358346370232669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31396715942905564246821779 47095073914358346370232669)
          ·
            refine ⟨17660652717884379888837251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47095073914358346370232669 17660652717884379888837251)
            ·
              refine ⟨26490979076826569833255877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17660652717884379888837251 26490979076826569833255877)
              ·
                refine ⟨4967058576904981843735477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26490979076826569833255877 4967058576904981843735477)
                ·
                  refine ⟨465661741584842047850201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4967058576904981843735477 465661741584842047850201)
                  ·
                    rfl

theorem cell23_8161857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 5].length) (baseStart_8161857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161857 prefixEnd_8161857 := by exact prefixLift 8161857
  have htrace : WordTrace (prefixWord ++ tailWord_8161857) baseStart_8161857 baseEnd_8161857 := by
    simpa [prefixWord, tailWord_8161857, baseEnd_8161857] using wordTrace_append hprefix tailTrace_8161857
  have hstable : (prefixWord ++ tailWord_8161857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161857).length < 2 ^ (prefixWord ++ tailWord_8161857).sum := by decide
  have hdescent : baseEnd_8161857 < baseStart_8161857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161903 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_8161903 : Nat := 118140960795 + 8161903 * 2 ^ 59
def prefixEnd_8161903 : Nat := 4983230072969 + 3 ^ 40 * 8161903 * 2
def baseEnd_8161903 : Nat := 4190979294373685250676597

theorem tailTrace_8161903 : CollatzResearch.WordTrace tailWord_8161903 prefixEnd_8161903 4190979294373685250676597 := by
  unfold tailWord_8161903
  simp only [CollatzResearch.WordTrace]
  refine ⟨297689058549826847900114363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198459372366551231933409575 297689058549826847900114363)
  ·
    refine ⟨446533587824740271850171545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297689058549826847900114363 446533587824740271850171545)
    ·
      refine ⟨334900190868555203887628659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446533587824740271850171545 334900190868555203887628659)
      ·
        refine ⟨502350286302832805831442989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334900190868555203887628659 502350286302832805831442989)
        ·
          refine ⟨188381357363562302186791121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502350286302832805831442989 188381357363562302186791121)
          ·
            refine ⟨141286018022671726640093341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188381357363562302186791121 141286018022671726640093341)
            ·
              refine ⟨52982256758501897490035003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141286018022671726640093341 52982256758501897490035003)
              ·
                refine ⟨79473385137752846235052505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52982256758501897490035003 79473385137752846235052505)
                ·
                  refine ⟨59605038853314634676289379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79473385137752846235052505 59605038853314634676289379)
                  ·
                    refine ⟨89407558279971952014434069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59605038853314634676289379 89407558279971952014434069)
                    ·
                      refine ⟨4190979294373685250676597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89407558279971952014434069 4190979294373685250676597)
                      ·
                        rfl

theorem cell23_8161903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_8161903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161903 prefixEnd_8161903 := by exact prefixLift 8161903
  have htrace : WordTrace (prefixWord ++ tailWord_8161903) baseStart_8161903 baseEnd_8161903 := by
    simpa [prefixWord, tailWord_8161903, baseEnd_8161903] using wordTrace_append hprefix tailTrace_8161903
  have hstable : (prefixWord ++ tailWord_8161903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161903).length < 2 ^ (prefixWord ++ tailWord_8161903).sum := by decide
  have hdescent : baseEnd_8161903 < baseStart_8161903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161967 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 4, 3, 2]
def baseStart_8161967 : Nat := 118140960795 + 8161967 * 2 ^ 59
def prefixEnd_8161967 : Nat := 4983230072969 + 3 ^ 40 * 8161967 * 2
def baseEnd_8161967 : Nat := 4191012157135573000276303

theorem tailTrace_8161967 : CollatzResearch.WordTrace tailWord_8161967 prefixEnd_8161967 4191012157135573000276303 := by
  unfold tailWord_8161967
  simp only [CollatzResearch.WordTrace]
  refine ⟨297691392821594986830444155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198460928547729991220296103 297691392821594986830444155)
  ·
    refine ⟨446537089232392480245666233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297691392821594986830444155 446537089232392480245666233)
    ·
      refine ⟨334902816924294360184249675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446537089232392480245666233 334902816924294360184249675)
      ·
        refine ⟨502354225386441540276374513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334902816924294360184249675 502354225386441540276374513)
        ·
          refine ⟨376765669039831155207280885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502354225386441540276374513 376765669039831155207280885)
          ·
            refine ⟨35321781472484170800682583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376765669039831155207280885 35321781472484170800682583)
            ·
              refine ⟨52982672208726256201023875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35321781472484170800682583 52982672208726256201023875)
              ·
                refine ⟨79474008313089384301535813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52982672208726256201023875 79474008313089384301535813)
                ·
                  refine ⟨14901376558704259556537965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79474008313089384301535813 14901376558704259556537965)
                  ·
                    refine ⟨5588016209514097333701737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14901376558704259556537965 5588016209514097333701737)
                    ·
                      refine ⟨4191012157135573000276303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588016209514097333701737 4191012157135573000276303)
                      ·
                        rfl

theorem cell23_8161967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3, 2].length) (baseStart_8161967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161967 prefixEnd_8161967 := by exact prefixLift 8161967
  have htrace : WordTrace (prefixWord ++ tailWord_8161967) baseStart_8161967 baseEnd_8161967 := by
    simpa [prefixWord, tailWord_8161967, baseEnd_8161967] using wordTrace_append hprefix tailTrace_8161967
  have hstable : (prefixWord ++ tailWord_8161967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161967).length < 2 ^ (prefixWord ++ tailWord_8161967).sum := by decide
  have hdescent : baseEnd_8161967 < baseStart_8161967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8161994 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_8161994 : Nat := 118140960795 + 8161994 * 2 ^ 59
def prefixEnd_8161994 : Nat := 4983230072969 + 3 ^ 40 * 8161994 * 2
def baseEnd_8161994 : Nat := 1397008673704414798212893

theorem tailTrace_8161994 : CollatzResearch.WordTrace tailWord_8161994 prefixEnd_8161994 1397008673704414798212893 := by
  unfold tailWord_8161994
  simp only [CollatzResearch.WordTrace]
  refine ⟨74423094398124292610419259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198461585061664780294451357 74423094398124292610419259)
  ·
    refine ⟨111634641597186438915628889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74423094398124292610419259 111634641597186438915628889)
    ·
      refine ⟨83725981197889829186721667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111634641597186438915628889 83725981197889829186721667)
      ·
        refine ⟨125588971796834743780082501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83725981197889829186721667 125588971796834743780082501)
        ·
          refine ⟨23547932211906514458765469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125588971796834743780082501 23547932211906514458765469)
          ·
            refine ⟨8830474579464942922037051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23547932211906514458765469 8830474579464942922037051)
            ·
              refine ⟨13245711869197414383055577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8830474579464942922037051 13245711869197414383055577)
              ·
                refine ⟨9934283901898060787291683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13245711869197414383055577 9934283901898060787291683)
                ·
                  refine ⟨14901425852847091180937525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934283901898060787291683 14901425852847091180937525)
                  ·
                    refine ⟨1397008673704414798212893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14901425852847091180937525 1397008673704414798212893)
                    ·
                      rfl

theorem cell23_8161994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_8161994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8161994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8161994 prefixEnd_8161994 := by exact prefixLift 8161994
  have htrace : WordTrace (prefixWord ++ tailWord_8161994) baseStart_8161994 baseEnd_8161994 := by
    simpa [prefixWord, tailWord_8161994, baseEnd_8161994] using wordTrace_append hprefix tailTrace_8161994
  have hstable : (prefixWord ++ tailWord_8161994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8161994).length < 2 ^ (prefixWord ++ tailWord_8161994).sum := by decide
  have hdescent : baseEnd_8161994 < baseStart_8161994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8161994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162017 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_8162017 : Nat := 118140960795 + 8162017 * 2 ^ 59
def prefixEnd_8162017 : Nat := 4983230072969 + 3 ^ 40 * 8162017 * 2
def baseEnd_8162017 : Nat := 4191037831168297804651073

theorem tailTrace_8162017 : CollatzResearch.WordTrace tailWord_8162017 prefixEnd_8162017 4191037831168297804651073 := by
  unfold tailWord_8162017
  simp only [CollatzResearch.WordTrace]
  refine ⟨297693216471413845369764305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198462144314275896913176203 297693216471413845369764305)
  ·
    refine ⟨223269912353560384027323229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297693216471413845369764305 223269912353560384027323229)
    ·
      refine ⟨83726217132585144010246211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223269912353560384027323229 83726217132585144010246211)
      ·
        refine ⟨125589325698877716015369317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83726217132585144010246211 125589325698877716015369317)
        ·
          refine ⟨23547998568539571752881747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125589325698877716015369317 23547998568539571752881747)
          ·
            refine ⟨35321997852809357629322621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23547998568539571752881747 35321997852809357629322621)
            ·
              refine ⟨13245749194803509110995983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35321997852809357629322621 13245749194803509110995983)
              ·
                refine ⟨19868623792205263666493975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13245749194803509110995983 19868623792205263666493975)
                ·
                  refine ⟨29802935688307895499740963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19868623792205263666493975 29802935688307895499740963)
                  ·
                    refine ⟨44704403532461843249611445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29802935688307895499740963 44704403532461843249611445)
                    ·
                      refine ⟨4191037831168297804651073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44704403532461843249611445 4191037831168297804651073)
                      ·
                        rfl

theorem cell23_8162017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_8162017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162017 prefixEnd_8162017 := by exact prefixLift 8162017
  have htrace : WordTrace (prefixWord ++ tailWord_8162017) baseStart_8162017 baseEnd_8162017 := by
    simpa [prefixWord, tailWord_8162017, baseEnd_8162017] using wordTrace_append hprefix tailTrace_8162017
  have hstable : (prefixWord ++ tailWord_8162017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162017).length < 2 ^ (prefixWord ++ tailWord_8162017).sum := by decide
  have hdescent : baseEnd_8162017 < baseStart_8162017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162047 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 3]
def baseStart_8162047 : Nat := 118140960795 + 8162047 * 2 ^ 59
def prefixEnd_8162047 : Nat := 4983230072969 + 3 ^ 40 * 8162047 * 2
def baseEnd_8162047 : Nat := 4191053235587932687275935

theorem tailTrace_8162047 : CollatzResearch.WordTrace tailWord_8162047 prefixEnd_8162047 4191053235587932687275935 := by
  unfold tailWord_8162047
  simp only [CollatzResearch.WordTrace]
  refine ⟨297694310661305160493356395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198462873774203440328904263 297694310661305160493356395)
  ·
    refine ⟨446541465991957740740034593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297694310661305160493356395 446541465991957740740034593)
    ·
      refine ⟨334906099493968305555025945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446541465991957740740034593 334906099493968305555025945)
      ·
        refine ⟨251179574620476229166269459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334906099493968305555025945 251179574620476229166269459)
        ·
          refine ⟨376769361930714343749404189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251179574620476229166269459 376769361930714343749404189)
          ·
            refine ⟨141288510724017878906026571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376769361930714343749404189 141288510724017878906026571)
            ·
              refine ⟨211932766086026818359039857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141288510724017878906026571 211932766086026818359039857)
              ·
                refine ⟨158949574564520113769279893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211932766086026818359039857 158949574564520113769279893)
                ·
                  refine ⟨7450761307711880332934995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158949574564520113769279893 7450761307711880332934995)
                  ·
                    refine ⟨11176141961567820499402493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7450761307711880332934995 11176141961567820499402493)
                    ·
                      refine ⟨4191053235587932687275935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176141961567820499402493 4191053235587932687275935)
                      ·
                        rfl

theorem cell23_8162047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_8162047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162047 prefixEnd_8162047 := by exact prefixLift 8162047
  have htrace : WordTrace (prefixWord ++ tailWord_8162047) baseStart_8162047 baseEnd_8162047 := by
    simpa [prefixWord, tailWord_8162047, baseEnd_8162047] using wordTrace_append hprefix tailTrace_8162047
  have hstable : (prefixWord ++ tailWord_8162047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162047).length < 2 ^ (prefixWord ++ tailWord_8162047).sum := by decide
  have hdescent : baseEnd_8162047 < baseStart_8162047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162060 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_8162060 : Nat := 118140960795 + 8162060 * 2 ^ 59
def prefixEnd_8162060 : Nat := 4983230072969 + 3 ^ 40 * 8162060 * 2
def baseEnd_8162060 : Nat := 4191059910836441136413375

theorem tailTrace_8162060 : CollatzResearch.WordTrace tailWord_8162060 prefixEnd_8162060 4191059910836441136413375 := by
  unfold tailWord_8162060
  simp only [CollatzResearch.WordTrace]
  refine ⟨148847392405129031856789817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198463189873505375809053089 148847392405129031856789817)
  ·
    refine ⟨111635544303846773892592363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148847392405129031856789817 111635544303846773892592363)
    ·
      refine ⟨167453316455770160838888545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111635544303846773892592363 167453316455770160838888545)
      ·
        refine ⟨125589987341827620629166409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167453316455770160838888545 125589987341827620629166409)
        ·
          refine ⟨94192490506370715471874807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125589987341827620629166409 94192490506370715471874807)
          ·
            refine ⟨141288735759556073207812211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94192490506370715471874807 141288735759556073207812211)
            ·
              refine ⟨211933103639334109811718317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141288735759556073207812211 211933103639334109811718317)
              ·
                refine ⟨79474913864750291179394369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211933103639334109811718317 79474913864750291179394369)
                ·
                  refine ⟨59606185398562718384545777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79474913864750291179394369 59606185398562718384545777)
                  ·
                    refine ⟨44704639048922038788409333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59606185398562718384545777 44704639048922038788409333)
                    ·
                      refine ⟨4191059910836441136413375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44704639048922038788409333 4191059910836441136413375)
                      ·
                        rfl

theorem cell23_8162060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_8162060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162060 prefixEnd_8162060 := by exact prefixLift 8162060
  have htrace : WordTrace (prefixWord ++ tailWord_8162060) baseStart_8162060 baseEnd_8162060 := by
    simpa [prefixWord, tailWord_8162060, baseEnd_8162060] using wordTrace_append hprefix tailTrace_8162060
  have hstable : (prefixWord ++ tailWord_8162060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162060).length < 2 ^ (prefixWord ++ tailWord_8162060).sum := by decide
  have hdescent : baseEnd_8162060 < baseStart_8162060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162157 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_8162157 : Nat := 118140960795 + 8162157 * 2 ^ 59
def prefixEnd_8162157 : Nat := 4983230072969 + 3 ^ 40 * 8162157 * 2
def baseEnd_8162157 : Nat := 1397036572819975752300143

theorem tailTrace_8162157 : CollatzResearch.WordTrace tailWord_8162157 prefixEnd_8162157 1397036572819975752300143 := by
  unfold tailWord_8162157
  simp only [CollatzResearch.WordTrace]
  refine ⟨297698322690906649279860725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198465548460604432853240483 297698322690906649279860725)
  ·
    refine ⟨27909217752272498369986943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297698322690906649279860725 27909217752272498369986943)
    ·
      refine ⟨41863826628408747554980415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27909217752272498369986943 41863826628408747554980415)
      ·
        refine ⟨62795739942613121332470623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41863826628408747554980415 62795739942613121332470623)
        ·
          refine ⟨94193609913919681998705935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62795739942613121332470623 94193609913919681998705935)
          ·
            refine ⟨141290414870879522998058903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94193609913919681998705935 141290414870879522998058903)
            ·
              refine ⟨211935622306319284497088355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141290414870879522998058903 211935622306319284497088355)
              ·
                refine ⟨317903433459478926745632533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211935622306319284497088355 317903433459478926745632533)
                ·
                  refine ⟨14901723443413074691201525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317903433459478926745632533 14901723443413074691201525)
                  ·
                    refine ⟨1397036572819975752300143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14901723443413074691201525 1397036572819975752300143)
                    ·
                      rfl

theorem cell23_8162157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_8162157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162157 prefixEnd_8162157 := by exact prefixLift 8162157
  have htrace : WordTrace (prefixWord ++ tailWord_8162157) baseStart_8162157 baseEnd_8162157 := by
    simpa [prefixWord, tailWord_8162157, baseEnd_8162157] using wordTrace_append hprefix tailTrace_8162157
  have hstable : (prefixWord ++ tailWord_8162157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162157).length < 2 ^ (prefixWord ++ tailWord_8162157).sum := by decide
  have hdescent : baseEnd_8162157 < baseStart_8162157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
