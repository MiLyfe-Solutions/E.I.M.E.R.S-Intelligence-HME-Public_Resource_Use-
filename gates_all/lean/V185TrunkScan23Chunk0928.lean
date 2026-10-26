import V185TrunkScan23Chunk0927

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5492826 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_5492826 : Nat := 118140960795 + 5492826 * 2 ^ 59
def prefixEnd_5492826 : Nat := 4983230072969 + 3 ^ 40 * 5492826 * 2
def baseEnd_5492826 : Nat := 313384432168136836301551

theorem tailTrace_5492826 : CollatzResearch.WordTrace tailWord_5492826 prefixEnd_5492826 313384432168136836301551 := by
  unfold tailWord_5492826
  simp only [CollatzResearch.WordTrace]
  refine ⟨50084955699609244209988583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133559881865624651226636221 50084955699609244209988583)
  ·
    refine ⟨75127433549413866314982875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50084955699609244209988583 75127433549413866314982875)
    ·
      refine ⟨112691150324120799472474313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75127433549413866314982875 112691150324120799472474313)
      ·
        refine ⟨84518362743090599604355735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112691150324120799472474313 84518362743090599604355735)
        ·
          refine ⟨126777544114635899406533603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84518362743090599604355735 126777544114635899406533603)
          ·
            refine ⟨190166316171953849109800405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126777544114635899406533603 190166316171953849109800405)
            ·
              refine ⟨4457023035280168338510947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190166316171953849109800405 4457023035280168338510947)
              ·
                refine ⟨6685534552920252507766421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457023035280168338510947 6685534552920252507766421)
                ·
                  refine ⟨313384432168136836301551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6685534552920252507766421 313384432168136836301551)
                  ·
                    rfl

theorem cell23_5492826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_5492826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492826 prefixEnd_5492826 := by exact prefixLift 5492826
  have htrace : WordTrace (prefixWord ++ tailWord_5492826) baseStart_5492826 baseEnd_5492826 := by
    simpa [prefixWord, tailWord_5492826, baseEnd_5492826] using wordTrace_append hprefix tailTrace_5492826
  have hstable : (prefixWord ++ tailWord_5492826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492826).length < 2 ^ (prefixWord ++ tailWord_5492826).sum := by decide
  have hdescent : baseEnd_5492826 < baseStart_5492826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492859 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 4]
def baseStart_5492859 : Nat := 118140960795 + 5492859 * 2 ^ 59
def prefixEnd_5492859 : Nat := 4983230072969 + 3 ^ 40 * 5492859 * 2
def baseEnd_5492859 : Nat := 2820476834374829897601307

theorem tailTrace_5492859 : CollatzResearch.WordTrace tailWord_5492859 prefixEnd_5492859 2820476834374829897601307 := by
  unfold tailWord_5492859
  simp only [CollatzResearch.WordTrace]
  refine ⟨200341026407317423475905631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133560684271544948983937087 200341026407317423475905631)
  ·
    refine ⟨300511539610976135213858447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200341026407317423475905631 300511539610976135213858447)
    ·
      refine ⟨450767309416464202820787671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300511539610976135213858447 450767309416464202820787671)
      ·
        refine ⟨676150964124696304231181507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450767309416464202820787671 676150964124696304231181507)
        ·
          refine ⟨1014226446187044456346772261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676150964124696304231181507 1014226446187044456346772261)
          ·
            refine ⟨190167458660070835565019799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1014226446187044456346772261 190167458660070835565019799)
            ·
              refine ⟨285251187990106253347529699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190167458660070835565019799 285251187990106253347529699)
              ·
                refine ⟨427876781985159380021294549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285251187990106253347529699 427876781985159380021294549)
                ·
                  refine ⟨10028362077777172969249091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 427876781985159380021294549 10028362077777172969249091)
                  ·
                    refine ⟨15042543116665759453873637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10028362077777172969249091 15042543116665759453873637)
                    ·
                      refine ⟨2820476834374829897601307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15042543116665759453873637 2820476834374829897601307)
                      ·
                        rfl

theorem cell23_5492859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 4].length) (baseStart_5492859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492859 prefixEnd_5492859 := by exact prefixLift 5492859
  have htrace : WordTrace (prefixWord ++ tailWord_5492859) baseStart_5492859 baseEnd_5492859 := by
    simpa [prefixWord, tailWord_5492859, baseEnd_5492859] using wordTrace_append hprefix tailTrace_5492859
  have hstable : (prefixWord ++ tailWord_5492859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492859).length < 2 ^ (prefixWord ++ tailWord_5492859).sum := by decide
  have hdescent : baseEnd_5492859 < baseStart_5492859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492889 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_5492889 : Nat := 118140960795 + 5492889 * 2 ^ 59
def prefixEnd_5492889 : Nat := 4983230072969 + 3 ^ 40 * 5492889 * 2
def baseEnd_5492889 : Nat := 2820492238794464780226169

theorem tailTrace_5492889 : CollatzResearch.WordTrace tailWord_5492889 prefixEnd_5492889 2820492238794464780226169 := by
  unfold tailWord_5492889
  simp only [CollatzResearch.WordTrace]
  refine ⟨200342120597208738599497721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133561413731472492399665147 200342120597208738599497721)
  ·
    refine ⟨150256590447906553949623291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200342120597208738599497721 150256590447906553949623291)
    ·
      refine ⟨225384885671859830924434937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150256590447906553949623291 225384885671859830924434937)
      ·
        refine ⟨169038664253894873193326203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225384885671859830924434937 169038664253894873193326203)
        ·
          refine ⟨253557996380842309789989305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169038664253894873193326203 253557996380842309789989305)
          ·
            refine ⟨190168497285631732342491979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253557996380842309789989305 190168497285631732342491979)
            ·
              refine ⟨285252745928447598513737969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190168497285631732342491979 285252745928447598513737969)
              ·
                refine ⟨213939559446335698885303477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285252745928447598513737969 213939559446335698885303477)
                ·
                  refine ⟨20056833698093971770497201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213939559446335698885303477 20056833698093971770497201)
                  ·
                    refine ⟨15042625273570478827872901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20056833698093971770497201 15042625273570478827872901)
                    ·
                      refine ⟨2820492238794464780226169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15042625273570478827872901 2820492238794464780226169)
                      ·
                        rfl

theorem cell23_5492889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_5492889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492889 prefixEnd_5492889 := by exact prefixLift 5492889
  have htrace : WordTrace (prefixWord ++ tailWord_5492889) baseStart_5492889 baseEnd_5492889 := by
    simpa [prefixWord, tailWord_5492889, baseEnd_5492889] using wordTrace_append hprefix tailTrace_5492889
  have hstable : (prefixWord ++ tailWord_5492889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492889).length < 2 ^ (prefixWord ++ tailWord_5492889).sum := by decide
  have hdescent : baseEnd_5492889 < baseStart_5492889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492890 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_5492890 : Nat := 118140960795 + 5492890 * 2 ^ 59
def prefixEnd_5492890 : Nat := 4983230072969 + 3 ^ 40 * 5492890 * 2
def baseEnd_5492890 : Nat := 940164250758373092104555

theorem tailTrace_5492890 : CollatzResearch.WordTrace tailWord_5492890 prefixEnd_5492890 940164250758373092104555 := by
  unfold tailWord_5492890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50085539267551278942571031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133561438046803410513522749 50085539267551278942571031)
  ·
    refine ⟨75128308901326918413856547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50085539267551278942571031 75128308901326918413856547)
    ·
      refine ⟨112692463351990377620784821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75128308901326918413856547 112692463351990377620784821)
      ·
        refine ⟨10564918439249097901948577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112692463351990377620784821 10564918439249097901948577)
        ·
          refine ⟨7923688829436823426461433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10564918439249097901948577 7923688829436823426461433)
          ·
            refine ⟨5942766622077617569846075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7923688829436823426461433 5942766622077617569846075)
            ·
              refine ⟨8914149933116426354769113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942766622077617569846075 8914149933116426354769113)
              ·
                refine ⟨6685612449837319766076835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8914149933116426354769113 6685612449837319766076835)
                ·
                  refine ⟨10028418674755979649115253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685612449837319766076835 10028418674755979649115253)
                  ·
                    refine ⟨940164250758373092104555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10028418674755979649115253 940164250758373092104555)
                    ·
                      rfl

theorem cell23_5492890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_5492890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492890 prefixEnd_5492890 := by exact prefixLift 5492890
  have htrace : WordTrace (prefixWord ++ tailWord_5492890) baseStart_5492890 baseEnd_5492890 := by
    simpa [prefixWord, tailWord_5492890, baseEnd_5492890] using wordTrace_append hprefix tailTrace_5492890
  have hstable : (prefixWord ++ tailWord_5492890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492890).length < 2 ^ (prefixWord ++ tailWord_5492890).sum := by decide
  have hdescent : baseEnd_5492890 < baseStart_5492890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492893 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_5492893 : Nat := 118140960795 + 5492893 * 2 ^ 59
def prefixEnd_5492893 : Nat := 4983230072969 + 3 ^ 40 * 5492893 * 2
def baseEnd_5492893 : Nat := 2820494292717082764576151

theorem tailTrace_5492893 : CollatzResearch.WordTrace tailWord_5492893 prefixEnd_5492893 2820494292717082764576151 := by
  unfold tailWord_5492893
  simp only [CollatzResearch.WordTrace]
  refine ⟨200342266489194247282643333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133561510992796164855095555 200342266489194247282643333)
  ·
    refine ⟨37564174966723921365495625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200342266489194247282643333 37564174966723921365495625)
    ·
      refine ⟨28173131225042941024121719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37564174966723921365495625 28173131225042941024121719)
      ·
        refine ⟨42259696837564411536182579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28173131225042941024121719 42259696837564411536182579)
        ·
          refine ⟨63389545256346617304273869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42259696837564411536182579 63389545256346617304273869)
          ·
            refine ⟨23771079471129981489102701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63389545256346617304273869 23771079471129981489102701)
            ·
              refine ⟨8914154801673743058413513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23771079471129981489102701 8914154801673743058413513)
              ·
                refine ⟨6685616101255307293810135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8914154801673743058413513 6685616101255307293810135)
                ·
                  refine ⟨10028424151882960940715203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685616101255307293810135 10028424151882960940715203)
                  ·
                    refine ⟨15042636227824441411072805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10028424151882960940715203 15042636227824441411072805)
                    ·
                      refine ⟨2820494292717082764576151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15042636227824441411072805 2820494292717082764576151)
                      ·
                        rfl

theorem cell23_5492893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_5492893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492893 prefixEnd_5492893 := by exact prefixLift 5492893
  have htrace : WordTrace (prefixWord ++ tailWord_5492893) baseStart_5492893 baseEnd_5492893 := by
    simpa [prefixWord, tailWord_5492893, baseEnd_5492893] using wordTrace_append hprefix tailTrace_5492893
  have hstable : (prefixWord ++ tailWord_5492893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492893).length < 2 ^ (prefixWord ++ tailWord_5492893).sum := by decide
  have hdescent : baseEnd_5492893 < baseStart_5492893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492903 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5492903 : Nat := 118140960795 + 5492903 * 2 ^ 59
def prefixEnd_5492903 : Nat := 4983230072969 + 3 ^ 40 * 5492903 * 2
def baseEnd_5492903 : Nat := 940166475841209241817035

theorem tailTrace_5492903 : CollatzResearch.WordTrace tailWord_5492903 prefixEnd_5492903 940166475841209241817035 := by
  unfold tailWord_5492903
  simp only [CollatzResearch.WordTrace]
  refine ⟨200342631219158018990507363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133561754146105345993671575 200342631219158018990507363)
  ·
    refine ⟨300513946828737028485761045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200342631219158018990507363 300513946828737028485761045)
    ·
      refine ⟨14086591257597048210270049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 300513946828737028485761045 14086591257597048210270049)
      ·
        refine ⟨10564943443197786157702537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14086591257597048210270049 10564943443197786157702537)
        ·
          refine ⟨7923707582398339618276903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10564943443197786157702537 7923707582398339618276903)
          ·
            refine ⟨11885561373597509427415355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7923707582398339618276903 11885561373597509427415355)
            ·
              refine ⟨17828342060396264141123033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11885561373597509427415355 17828342060396264141123033)
              ·
                refine ⟨13371256545297198105842275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17828342060396264141123033 13371256545297198105842275)
                ·
                  refine ⟨20056884817945797158763413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13371256545297198105842275 20056884817945797158763413)
                  ·
                    refine ⟨940166475841209241817035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20056884817945797158763413 940166475841209241817035)
                    ·
                      rfl

theorem cell23_5492903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5492903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492903 prefixEnd_5492903 := by exact prefixLift 5492903
  have htrace : WordTrace (prefixWord ++ tailWord_5492903) baseStart_5492903 baseEnd_5492903 := by
    simpa [prefixWord, tailWord_5492903, baseEnd_5492903] using wordTrace_append hprefix tailTrace_5492903
  have hstable : (prefixWord ++ tailWord_5492903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492903).length < 2 ^ (prefixWord ++ tailWord_5492903).sum := by decide
  have hdescent : baseEnd_5492903 < baseStart_5492903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492940 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5492940 : Nat := 118140960795 + 5492940 * 2 ^ 59
def prefixEnd_5492940 : Nat := 4983230072969 + 3 ^ 40 * 5492940 * 2
def baseEnd_5492940 : Nat := 2820518426307844080688435

theorem tailTrace_5492940 : CollatzResearch.WordTrace tailWord_5492940 prefixEnd_5492940 2820518426307844080688435 := by
  unfold tailWord_5492940
  simp only [CollatzResearch.WordTrace]
  refine ⟨100171990360011987154802137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133562653813349316206402849 100171990360011987154802137)
  ·
    refine ⟨75128992770008990366101603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100171990360011987154802137 75128992770008990366101603)
    ·
      refine ⟨112693489155013485549152405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75128992770008990366101603 112693489155013485549152405)
      ·
        refine ⟨5282507304141257135116519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112693489155013485549152405 5282507304141257135116519)
        ·
          refine ⟨7923760956211885702674779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282507304141257135116519 7923760956211885702674779)
          ·
            refine ⟨11885641434317828554012169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7923760956211885702674779 11885641434317828554012169)
            ·
              refine ⟨8914231075738371415509127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11885641434317828554012169 8914231075738371415509127)
              ·
                refine ⟨13371346613607557123263691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914231075738371415509127 13371346613607557123263691)
                ·
                  refine ⟨20057019920411335684895537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13371346613607557123263691 20057019920411335684895537)
                  ·
                    refine ⟨15042764940308501763671653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20057019920411335684895537 15042764940308501763671653)
                    ·
                      refine ⟨2820518426307844080688435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15042764940308501763671653 2820518426307844080688435)
                      ·
                        rfl

theorem cell23_5492940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5492940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492940 prefixEnd_5492940 := by exact prefixLift 5492940
  have htrace : WordTrace (prefixWord ++ tailWord_5492940) baseStart_5492940 baseEnd_5492940 := by
    simpa [prefixWord, tailWord_5492940, baseEnd_5492940] using wordTrace_append hprefix tailTrace_5492940
  have hstable : (prefixWord ++ tailWord_5492940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492940).length < 2 ^ (prefixWord ++ tailWord_5492940).sum := by decide
  have hdescent : baseEnd_5492940 < baseStart_5492940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492943 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 3]
def baseStart_5492943 : Nat := 118140960795 + 5492943 * 2 ^ 59
def prefixEnd_5492943 : Nat := 4983230072969 + 3 ^ 40 * 5492943 * 2
def baseEnd_5492943 : Nat := 2820519966749807568950921

theorem tailTrace_5492943 : CollatzResearch.WordTrace tailWord_5492943 prefixEnd_5492943 2820519966749807568950921 := by
  unfold tailWord_5492943
  simp only [CollatzResearch.WordTrace]
  refine ⟨200344090139013105821963483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133562726759342070547975655 200344090139013105821963483)
  ·
    refine ⟨300516135208519658732945225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200344090139013105821963483 300516135208519658732945225)
    ·
      refine ⟨225387101406389744049708919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300516135208519658732945225 225387101406389744049708919)
      ·
        refine ⟨338080652109584616074563379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225387101406389744049708919 338080652109584616074563379)
        ·
          refine ⟨507120978164376924111845069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338080652109584616074563379 507120978164376924111845069)
          ·
            refine ⟨190170366811641346541941901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507120978164376924111845069 190170366811641346541941901)
            ·
              refine ⟨71313887554365504953228213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190170366811641346541941901 71313887554365504953228213)
              ·
                refine ⟨6685676958221766089365145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71313887554365504953228213 6685676958221766089365145)
                ·
                  refine ⟨5014257718666324567023859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6685676958221766089365145 5014257718666324567023859)
                  ·
                    refine ⟨7521386577999486850535789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5014257718666324567023859 7521386577999486850535789)
                    ·
                      refine ⟨2820519966749807568950921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7521386577999486850535789 2820519966749807568950921)
                      ·
                        rfl

theorem cell23_5492943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_5492943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492943 prefixEnd_5492943 := by exact prefixLift 5492943
  have htrace : WordTrace (prefixWord ++ tailWord_5492943) baseStart_5492943 baseEnd_5492943 := by
    simpa [prefixWord, tailWord_5492943, baseEnd_5492943] using wordTrace_append hprefix tailTrace_5492943
  have hstable : (prefixWord ++ tailWord_5492943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492943).length < 2 ^ (prefixWord ++ tailWord_5492943).sum := by decide
  have hdescent : baseEnd_5492943 < baseStart_5492943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492950 : List Nat := [5, 2, 1, 2, 1, 2, 3, 7]
def baseStart_5492950 : Nat := 118140960795 + 5492950 * 2 ^ 59
def prefixEnd_5492950 : Nat := 4983230072969 + 3 ^ 40 * 5492950 * 2
def baseEnd_5492950 : Nat := 104463835596829223761607

theorem tailTrace_5492950 : CollatzResearch.WordTrace tailWord_5492950 prefixEnd_5492950 104463835596829223761607 := by
  unfold tailWord_5492950
  simp only [CollatzResearch.WordTrace]
  refine ⟨12521521590624234126091769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133562896966658497344978869 12521521590624234126091769)
  ·
    refine ⟨9391141192968175594568827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12521521590624234126091769 9391141192968175594568827)
    ·
      refine ⟨14086711789452263391853241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391141192968175594568827 14086711789452263391853241)
      ·
        refine ⟨10565033842089197543889931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14086711789452263391853241 10565033842089197543889931)
        ·
          refine ⟨15847550763133796315834897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10565033842089197543889931 15847550763133796315834897)
          ·
            refine ⟨11885663072350347236876173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15847550763133796315834897 11885663072350347236876173)
            ·
              refine ⟨4457123652131380213828565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11885663072350347236876173 4457123652131380213828565)
              ·
                refine ⟨104463835596829223761607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4457123652131380213828565 104463835596829223761607)
                ·
                  rfl

theorem cell23_5492950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_5492950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492950 prefixEnd_5492950 := by exact prefixLift 5492950
  have htrace : WordTrace (prefixWord ++ tailWord_5492950) baseStart_5492950 baseEnd_5492950 := by
    simpa [prefixWord, tailWord_5492950, baseEnd_5492950] using wordTrace_append hprefix tailTrace_5492950
  have hstable : (prefixWord ++ tailWord_5492950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492950).length < 2 ^ (prefixWord ++ tailWord_5492950).sum := by decide
  have hdescent : baseEnd_5492950 < baseStart_5492950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492953 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 3, 3, 2]
def baseStart_5492953 : Nat := 118140960795 + 5492953 * 2 ^ 59
def prefixEnd_5492953 : Nat := 4983230072969 + 3 ^ 40 * 5492953 * 2
def baseEnd_5492953 : Nat := 2820525101556352529825875

theorem tailTrace_5492953 : CollatzResearch.WordTrace tailWord_5492953 prefixEnd_5492953 2820525101556352529825875 := by
  unfold tailWord_5492953
  simp only [CollatzResearch.WordTrace]
  refine ⟨200344454868976877529827513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133562969912651251686551675 200344454868976877529827513)
  ·
    refine ⟨150258341151732658147370635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200344454868976877529827513 150258341151732658147370635)
    ·
      refine ⟨225387511727598987221055953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150258341151732658147370635 225387511727598987221055953)
      ·
        refine ⟨169040633795699240415791965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225387511727598987221055953 169040633795699240415791965)
        ·
          refine ⟨63390237673387215155921987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169040633795699240415791965 63390237673387215155921987)
          ·
            refine ⟨95085356510080822733882981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63390237673387215155921987 95085356510080822733882981)
            ·
              refine ⟨17828504345640154262603059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95085356510080822733882981 17828504345640154262603059)
              ·
                refine ⟨26742756518460231393904589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17828504345640154262603059 26742756518460231393904589)
                ·
                  refine ⟨10028533694422586772714221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26742756518460231393904589 10028533694422586772714221)
                  ·
                    refine ⟨3760700135408470039767833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10028533694422586772714221 3760700135408470039767833)
                    ·
                      refine ⟨2820525101556352529825875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760700135408470039767833 2820525101556352529825875)
                      ·
                        rfl

theorem cell23_5492953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_5492953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492953 prefixEnd_5492953 := by exact prefixLift 5492953
  have htrace : WordTrace (prefixWord ++ tailWord_5492953) baseStart_5492953 baseEnd_5492953 := by
    simpa [prefixWord, tailWord_5492953, baseEnd_5492953] using wordTrace_append hprefix tailTrace_5492953
  have hstable : (prefixWord ++ tailWord_5492953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492953).length < 2 ^ (prefixWord ++ tailWord_5492953).sum := by decide
  have hdescent : baseEnd_5492953 < baseStart_5492953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492959 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 8]
def baseStart_5492959 : Nat := 118140960795 + 5492959 * 2 ^ 59
def prefixEnd_5492959 : Nat := 4983230072969 + 3 ^ 40 * 5492959 * 2
def baseEnd_5492959 : Nat := 940176060813426502116949

theorem tailTrace_5492959 : CollatzResearch.WordTrace tailWord_5492959 prefixEnd_5492959 940176060813426502116949 := by
  unfold tailWord_5492959
  simp only [CollatzResearch.WordTrace]
  refine ⟨200344673706955140554545931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133563115804636760369697287 200344673706955140554545931)
  ·
    refine ⟨300517010560432710831818897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200344673706955140554545931 300517010560432710831818897)
    ·
      refine ⟨225387757920324533123864173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300517010560432710831818897 225387757920324533123864173)
      ·
        refine ⟨84520409220121699921449065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225387757920324533123864173 84520409220121699921449065)
        ·
          refine ⟨63390306915091274941086799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84520409220121699921449065 63390306915091274941086799)
          ·
            refine ⟨95085460372636912411630199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63390306915091274941086799 95085460372636912411630199)
            ·
              refine ⟨142628190558955368617445299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95085460372636912411630199 142628190558955368617445299)
              ·
                refine ⟨213942285838433052926167949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142628190558955368617445299 213942285838433052926167949)
                ·
                  refine ⟨80228357189412394847312981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213942285838433052926167949 80228357189412394847312981)
                  ·
                    refine ⟨940176060813426502116949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80228357189412394847312981 940176060813426502116949)
                    ·
                      rfl

theorem cell23_5492959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_5492959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492959 prefixEnd_5492959 := by exact prefixLift 5492959
  have htrace : WordTrace (prefixWord ++ tailWord_5492959) baseStart_5492959 baseEnd_5492959 := by
    simpa [prefixWord, tailWord_5492959, baseEnd_5492959] using wordTrace_append hprefix tailTrace_5492959
  have hstable : (prefixWord ++ tailWord_5492959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492959).length < 2 ^ (prefixWord ++ tailWord_5492959).sum := by decide
  have hdescent : baseEnd_5492959 < baseStart_5492959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492970 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_5492970 : Nat := 118140960795 + 5492970 * 2 ^ 59
def prefixEnd_5492970 : Nat := 4983230072969 + 3 ^ 40 * 5492970 * 2
def baseEnd_5492970 : Nat := 2820533830727478963313297

theorem tailTrace_5492970 : CollatzResearch.WordTrace tailWord_5492970 prefixEnd_5492970 2820533830727478963313297 := by
  unfold tailWord_5492970
  simp only [CollatzResearch.WordTrace]
  refine ⟨50086268727478822358299091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133563383273276859622130909 50086268727478822358299091)
  ·
    refine ⟨75129403091218233537448637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50086268727478822358299091 75129403091218233537448637)
    ·
      refine ⟨28173526159206837576543239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75129403091218233537448637 28173526159206837576543239)
      ·
        refine ⟨42260289238810256364814859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28173526159206837576543239 42260289238810256364814859)
        ·
          refine ⟨63390433858215384547222289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42260289238810256364814859 63390433858215384547222289)
          ·
            refine ⟨47542825393661538410416717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63390433858215384547222289 47542825393661538410416717)
            ·
              refine ⟨17828559522623076903906269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47542825393661538410416717 17828559522623076903906269)
              ·
                refine ⟨6685709820983653838964851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17828559522623076903906269 6685709820983653838964851)
                ·
                  refine ⟨10028564731475480758447277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685709820983653838964851 10028564731475480758447277)
                  ·
                    refine ⟨3760711774303305284417729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10028564731475480758447277 3760711774303305284417729)
                    ·
                      refine ⟨2820533830727478963313297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760711774303305284417729 2820533830727478963313297)
                      ·
                        rfl

theorem cell23_5492970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_5492970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492970 prefixEnd_5492970 := by exact prefixLift 5492970
  have htrace : WordTrace (prefixWord ++ tailWord_5492970) baseStart_5492970 baseEnd_5492970 := by
    simpa [prefixWord, tailWord_5492970, baseEnd_5492970] using wordTrace_append hprefix tailTrace_5492970
  have hstable : (prefixWord ++ tailWord_5492970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492970).length < 2 ^ (prefixWord ++ tailWord_5492970).sum := by decide
  have hdescent : baseEnd_5492970 < baseStart_5492970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492994 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_5492994 : Nat := 118140960795 + 5492994 * 2 ^ 59
def prefixEnd_5492994 : Nat := 4983230072969 + 3 ^ 40 * 5492994 * 2
def baseEnd_5492994 : Nat := 2820546154263186869413187

theorem tailTrace_5492994 : CollatzResearch.WordTrace tailWord_5492994 prefixEnd_5492994 2820546154263186869413187 := by
  unfold tailWord_5492994
  simp only [CollatzResearch.WordTrace]
  refine ⟨50086487565457085383017509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133563966841218894354713357 50086487565457085383017509)
  ·
    refine ⟨9391216418523203509315783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50086487565457085383017509 9391216418523203509315783)
    ·
      refine ⟨14086824627784805263973675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391216418523203509315783 14086824627784805263973675)
      ·
        refine ⟨21130236941677207895960513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14086824627784805263973675 21130236941677207895960513)
        ·
          refine ⟨15847677706257905921970385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21130236941677207895960513 15847677706257905921970385)
          ·
            refine ⟨11885758279693429441477789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15847677706257905921970385 11885758279693429441477789)
            ·
              refine ⟨4457159354885036040554171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11885758279693429441477789 4457159354885036040554171)
              ·
                refine ⟨6685739032327554060831257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457159354885036040554171 6685739032327554060831257)
                ·
                  refine ⟨5014304274245665545623443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6685739032327554060831257 5014304274245665545623443)
                  ·
                    refine ⟨7521456411368498318435165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5014304274245665545623443 7521456411368498318435165)
                    ·
                      refine ⟨2820546154263186869413187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7521456411368498318435165 2820546154263186869413187)
                      ·
                        rfl

theorem cell23_5492994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_5492994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492994 prefixEnd_5492994 := by exact prefixLift 5492994
  have htrace : WordTrace (prefixWord ++ tailWord_5492994) baseStart_5492994 baseEnd_5492994 := by
    simpa [prefixWord, tailWord_5492994, baseEnd_5492994] using wordTrace_append hprefix tailTrace_5492994
  have hstable : (prefixWord ++ tailWord_5492994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492994).length < 2 ^ (prefixWord ++ tailWord_5492994).sum := by decide
  have hdescent : baseEnd_5492994 < baseStart_5492994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493000 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_5493000 : Nat := 118140960795 + 5493000 * 2 ^ 59
def prefixEnd_5493000 : Nat := 4983230072969 + 3 ^ 40 * 5493000 * 2
def baseEnd_5493000 : Nat := 2820549235147113845938159

theorem tailTrace_5493000 : CollatzResearch.WordTrace tailWord_5493000 prefixEnd_5493000 2820549235147113845938159 := by
  unfold tailWord_5493000
  simp only [CollatzResearch.WordTrace]
  refine ⟨100173084549903302278394227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133564112733204403037858969 100173084549903302278394227)
  ·
    refine ⟨150259626824854953417591341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100173084549903302278394227 150259626824854953417591341)
    ·
      refine ⟨56347360059320607531596753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150259626824854953417591341 56347360059320607531596753)
      ·
        refine ⟨42260520044490455648697565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56347360059320607531596753 42260520044490455648697565)
        ·
          refine ⟨15847695016683920868261587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42260520044490455648697565 15847695016683920868261587)
          ·
            refine ⟨23771542525025881302392381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15847695016683920868261587 23771542525025881302392381)
            ·
              refine ⟨8914328446884705488397143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23771542525025881302392381 8914328446884705488397143)
              ·
                refine ⟨13371492670327058232595715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914328446884705488397143 13371492670327058232595715)
                ·
                  refine ⟨20057239005490587348893573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13371492670327058232595715 20057239005490587348893573)
                  ·
                    refine ⟨3760732313529485127917545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20057239005490587348893573 3760732313529485127917545)
                    ·
                      refine ⟨2820549235147113845938159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760732313529485127917545 2820549235147113845938159)
                      ·
                        rfl

theorem cell23_5493000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_5493000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493000 prefixEnd_5493000 := by exact prefixLift 5493000
  have htrace : WordTrace (prefixWord ++ tailWord_5493000) baseStart_5493000 baseEnd_5493000 := by
    simpa [prefixWord, tailWord_5493000, baseEnd_5493000] using wordTrace_append hprefix tailTrace_5493000
  have hstable : (prefixWord ++ tailWord_5493000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493000).length < 2 ^ (prefixWord ++ tailWord_5493000).sum := by decide
  have hdescent : baseEnd_5493000 < baseStart_5493000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493006 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_5493006 : Nat := 118140960795 + 5493006 * 2 ^ 59
def prefixEnd_5493006 : Nat := 4983230072969 + 3 ^ 40 * 5493006 * 2
def baseEnd_5493006 : Nat := 313394701781226758051459

theorem tailTrace_5493006 : CollatzResearch.WordTrace tailWord_5493006 prefixEnd_5493006 313394701781226758051459 := by
  unfold tailWord_5493006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25043298492223108447688359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133564258625189911721004581 25043298492223108447688359)
  ·
    refine ⟨37564947738334662671532539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25043298492223108447688359 37564947738334662671532539)
    ·
      refine ⟨56347421607501994007298809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37564947738334662671532539 56347421607501994007298809)
      ·
        refine ⟨42260566205626495505474107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56347421607501994007298809 42260566205626495505474107)
        ·
          refine ⟨63390849308439743258211161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42260566205626495505474107 63390849308439743258211161)
          ·
            refine ⟨47543136981329807443658371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63390849308439743258211161 47543136981329807443658371)
            ·
              refine ⟨71314705471994711165487557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47543136981329807443658371 71314705471994711165487557)
              ·
                refine ⟨13371507275999008343528917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71314705471994711165487557 13371507275999008343528917)
                ·
                  refine ⟨313394701781226758051459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13371507275999008343528917 313394701781226758051459)
                  ·
                    rfl

theorem cell23_5493006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_5493006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493006 prefixEnd_5493006 := by exact prefixLift 5493006
  have htrace : WordTrace (prefixWord ++ tailWord_5493006) baseStart_5493006 baseEnd_5493006 := by
    simpa [prefixWord, tailWord_5493006, baseEnd_5493006] using wordTrace_append hprefix tailTrace_5493006
  have hstable : (prefixWord ++ tailWord_5493006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493006).length < 2 ^ (prefixWord ++ tailWord_5493006).sum := by decide
  have hdescent : baseEnd_5493006 < baseStart_5493006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493036 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_5493036 : Nat := 118140960795 + 5493036 * 2 ^ 59
def prefixEnd_5493036 : Nat := 4983230072969 + 3 ^ 40 * 5493036 * 2
def baseEnd_5493036 : Nat := 940189240150225235029331

theorem tailTrace_5493036 : CollatzResearch.WordTrace tailWord_5493036 prefixEnd_5493036 940189240150225235029331 := by
  unfold tailWord_5493036
  simp only [CollatzResearch.WordTrace]
  refine ⟨100173741063838091352549481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133564988085117455136732641 100173741063838091352549481)
  ·
    refine ⟨75130305797878568514412111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100173741063838091352549481 75130305797878568514412111)
    ·
      refine ⟨112695458696817852771618167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75130305797878568514412111 112695458696817852771618167)
      ·
        refine ⟨169043188045226779157427251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112695458696817852771618167 169043188045226779157427251)
        ·
          refine ⟨253564782067840168736140877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169043188045226779157427251 253564782067840168736140877)
          ·
            refine ⟨95086793275440063276052829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253564782067840168736140877 95086793275440063276052829)
            ·
              refine ⟨35657547478290023728519811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95086793275440063276052829 35657547478290023728519811)
              ·
                refine ⟨53486321217435035592779717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35657547478290023728519811 53486321217435035592779717)
                ·
                  refine ⟨10028685228269069173646197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53486321217435035592779717 10028685228269069173646197)
                  ·
                    refine ⟨940189240150225235029331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10028685228269069173646197 940189240150225235029331)
                    ·
                      rfl

theorem cell23_5493036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_5493036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493036 prefixEnd_5493036 := by exact prefixLift 5493036
  have htrace : WordTrace (prefixWord ++ tailWord_5493036) baseStart_5493036 baseEnd_5493036 := by
    simpa [prefixWord, tailWord_5493036, baseEnd_5493036] using wordTrace_append hprefix tailTrace_5493036
  have hstable : (prefixWord ++ tailWord_5493036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493036).length < 2 ^ (prefixWord ++ tailWord_5493036).sum := by decide
  have hdescent : baseEnd_5493036 < baseStart_5493036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493043 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 2, 5, 2]
def baseStart_5493043 : Nat := 118140960795 + 5493043 * 2 ^ 59
def prefixEnd_5493043 : Nat := 4983230072969 + 3 ^ 40 * 5493043 * 2
def baseEnd_5493043 : Nat := 2820571314815257177700461

theorem tailTrace_5493043 : CollatzResearch.WordTrace tailWord_5493043 prefixEnd_5493043 2820571314815257177700461 := by
  unfold tailWord_5493043
  simp only [CollatzResearch.WordTrace]
  refine ⟨200347737438650822900603783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133565158292433881933735855 200347737438650822900603783)
  ·
    refine ⟨300521606157976234350905675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200347737438650822900603783 300521606157976234350905675)
    ·
      refine ⟨450782409236964351526358513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300521606157976234350905675 450782409236964351526358513)
      ·
        refine ⟨338086806927723263644768885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450782409236964351526358513 338086806927723263644768885)
        ·
          refine ⟨31695638149474055966697083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338086806927723263644768885 31695638149474055966697083)
          ·
            refine ⟨47543457224211083950045625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31695638149474055966697083 47543457224211083950045625)
            ·
              refine ⟨35657592918158312962534219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47543457224211083950045625 35657592918158312962534219)
              ·
                refine ⟨53486389377237469443801329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35657592918158312962534219 53486389377237469443801329)
                ·
                  refine ⟨40114792032928102082850997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53486389377237469443801329 40114792032928102082850997)
                  ·
                    refine ⟨3760761753087009570267281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40114792032928102082850997 3760761753087009570267281)
                    ·
                      refine ⟨2820571314815257177700461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760761753087009570267281 2820571314815257177700461)
                      ·
                        rfl

theorem cell23_5493043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5, 2].length) (baseStart_5493043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493043 prefixEnd_5493043 := by exact prefixLift 5493043
  have htrace : WordTrace (prefixWord ++ tailWord_5493043) baseStart_5493043 baseEnd_5493043 := by
    simpa [prefixWord, tailWord_5493043, baseEnd_5493043] using wordTrace_append hprefix tailTrace_5493043
  have hstable : (prefixWord ++ tailWord_5493043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493043).length < 2 ^ (prefixWord ++ tailWord_5493043).sum := by decide
  have hdescent : baseEnd_5493043 < baseStart_5493043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493056 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_5493056 : Nat := 118140960795 + 5493056 * 2 ^ 59
def prefixEnd_5493056 : Nat := 4983230072969 + 3 ^ 40 * 5493056 * 2
def baseEnd_5493056 : Nat := 2820577990063765626837901

theorem tailTrace_5493056 : CollatzResearch.WordTrace tailWord_5493056 prefixEnd_5493056 2820577990063765626837901 := by
  unfold tailWord_5493056
  simp only [CollatzResearch.WordTrace]
  refine ⟨100174105793801863060413511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133565474391735817413884681 100174105793801863060413511)
  ·
    refine ⟨150261158690702794590620267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100174105793801863060413511 150261158690702794590620267)
    ·
      refine ⟨225391738036054191885930401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150261158690702794590620267 225391738036054191885930401)
      ·
        refine ⟨169043803527040643914447801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225391738036054191885930401 169043803527040643914447801)
        ·
          refine ⟨126782852645280482935835851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169043803527040643914447801 126782852645280482935835851)
          ·
            refine ⟨190174278967920724403753777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126782852645280482935835851 190174278967920724403753777)
            ·
              refine ⟨142630709225940543302815333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190174278967920724403753777 142630709225940543302815333)
              ·
                refine ⟨26743257979863851869277875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142630709225940543302815333 26743257979863851869277875)
                ·
                  refine ⟨40114886969795777803916813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26743257979863851869277875 40114886969795777803916813)
                  ·
                    refine ⟨15043082613673416676468805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40114886969795777803916813 15043082613673416676468805)
                    ·
                      refine ⟨2820577990063765626837901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15043082613673416676468805 2820577990063765626837901)
                      ·
                        rfl

theorem cell23_5493056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_5493056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493056 prefixEnd_5493056 := by exact prefixLift 5493056
  have htrace : WordTrace (prefixWord ++ tailWord_5493056) baseStart_5493056 baseEnd_5493056 := by
    simpa [prefixWord, tailWord_5493056, baseEnd_5493056] using wordTrace_append hprefix tailTrace_5493056
  have hstable : (prefixWord ++ tailWord_5493056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493056).length < 2 ^ (prefixWord ++ tailWord_5493056).sum := by decide
  have hdescent : baseEnd_5493056 < baseStart_5493056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493073 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_5493073 : Nat := 118140960795 + 5493073 * 2 ^ 59
def prefixEnd_5493073 : Nat := 4983230072969 + 3 ^ 40 * 5493073 * 2
def baseEnd_5493073 : Nat := 2820586719234892060325323

theorem tailTrace_5493073 : CollatzResearch.WordTrace tailWord_5493073 prefixEnd_5493073 2820586719234892060325323 := by
  unfold tailWord_5493073
  simp only [CollatzResearch.WordTrace]
  refine ⟨200348831628542138024195873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133565887752361425349463915 200348831628542138024195873)
  ·
    refine ⟨150261623721406603518146905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200348831628542138024195873 150261623721406603518146905)
    ·
      refine ⟨112696217791054952638610179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150261623721406603518146905 112696217791054952638610179)
      ·
        refine ⟨169044326686582428957915269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112696217791054952638610179 169044326686582428957915269)
        ·
          refine ⟨31695811253734205429609113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169044326686582428957915269 31695811253734205429609113)
          ·
            refine ⟨23771858440300654072206835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31695811253734205429609113 23771858440300654072206835)
            ·
              refine ⟨35657787660450981108310253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23771858440300654072206835 35657787660450981108310253)
              ·
                refine ⟨13371670372669117915616345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35657787660450981108310253 13371670372669117915616345)
                ·
                  refine ⟨10028752779501838436712259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13371670372669117915616345 10028752779501838436712259)
                  ·
                    refine ⟨15043129169252757655068389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10028752779501838436712259 15043129169252757655068389)
                    ·
                      refine ⟨2820586719234892060325323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15043129169252757655068389 2820586719234892060325323)
                      ·
                        rfl

theorem cell23_5493073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_5493073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493073 prefixEnd_5493073 := by exact prefixLift 5493073
  have htrace : WordTrace (prefixWord ++ tailWord_5493073) baseStart_5493073 baseEnd_5493073 := by
    simpa [prefixWord, tailWord_5493073, baseEnd_5493073] using wordTrace_append hprefix tailTrace_5493073
  have hstable : (prefixWord ++ tailWord_5493073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493073).length < 2 ^ (prefixWord ++ tailWord_5493073).sum := by decide
  have hdescent : baseEnd_5493073 < baseStart_5493073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493090 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5493090 : Nat := 118140960795 + 5493090 * 2 ^ 59
def prefixEnd_5493090 : Nat := 4983230072969 + 3 ^ 40 * 5493090 * 2
def baseEnd_5493090 : Nat := 2820595448406018493812745

theorem tailTrace_5493090 : CollatzResearch.WordTrace tailWord_5493090 prefixEnd_5493090 2820595448406018493812745 := by
  unfold tailWord_5493090
  simp only [CollatzResearch.WordTrace]
  refine ⟨50087362917370137481891181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133566301112987033285043149 50087362917370137481891181)
  ·
    refine ⟨18782761094013801555709193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50087362917370137481891181 18782761094013801555709193)
    ·
      refine ⟨14087070820510351166781895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18782761094013801555709193 14087070820510351166781895)
      ·
        refine ⟨21130606230765526750172843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14087070820510351166781895 21130606230765526750172843)
        ·
          refine ⟨31695909346148290125259265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21130606230765526750172843 31695909346148290125259265)
          ·
            refine ⟨23771932009611217593944449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31695909346148290125259265 23771932009611217593944449)
            ·
              refine ⟨17828949007208413195458337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23771932009611217593944449 17828949007208413195458337)
              ·
                refine ⟨13371711755406309896593753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17828949007208413195458337 13371711755406309896593753)
                ·
                  refine ⟨10028783816554732422445315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13371711755406309896593753 10028783816554732422445315)
                  ·
                    refine ⟨15043175724832098633667973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10028783816554732422445315 15043175724832098633667973)
                    ·
                      refine ⟨2820595448406018493812745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15043175724832098633667973 2820595448406018493812745)
                      ·
                        rfl

theorem cell23_5493090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5493090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493090 prefixEnd_5493090 := by exact prefixLift 5493090
  have htrace : WordTrace (prefixWord ++ tailWord_5493090) baseStart_5493090 baseEnd_5493090 := by
    simpa [prefixWord, tailWord_5493090, baseEnd_5493090] using wordTrace_append hprefix tailTrace_5493090
  have hstable : (prefixWord ++ tailWord_5493090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493090).length < 2 ^ (prefixWord ++ tailWord_5493090).sum := by decide
  have hdescent : baseEnd_5493090 < baseStart_5493090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493116 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_5493116 : Nat := 118140960795 + 5493116 * 2 ^ 59
def prefixEnd_5493116 : Nat := 4983230072969 + 3 ^ 40 * 5493116 * 2
def baseEnd_5493116 : Nat := 2820608798903035392087625

theorem tailTrace_5493116 : CollatzResearch.WordTrace tailWord_5493116 prefixEnd_5493116 2820608798903035392087625 := by
  unfold tailWord_5493116
  simp only [CollatzResearch.WordTrace]
  refine ⟨100175199983693178184005601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133566933311590904245340801 100175199983693178184005601)
  ·
    refine ⟨75131399987769883638004201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100175199983693178184005601 75131399987769883638004201)
    ·
      refine ⟨56348549990827412728503151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75131399987769883638004201 56348549990827412728503151)
      ·
        refine ⟨84522824986241119092754727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56348549990827412728503151 84522824986241119092754727)
        ·
          refine ⟨126784237479361678639132091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84522824986241119092754727 126784237479361678639132091)
          ·
            refine ⟨190176356219042517958698137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126784237479361678639132091 190176356219042517958698137)
            ·
              refine ⟨142632267164281888469023603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190176356219042517958698137 142632267164281888469023603)
              ·
                refine ⟨213948400746422832703535405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142632267164281888469023603 213948400746422832703535405)
                ·
                  refine ⟨80230650279908562263825777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213948400746422832703535405 80230650279908562263825777)
                  ·
                    refine ⟨60172987709931421697869333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80230650279908562263825777 60172987709931421697869333)
                    ·
                      refine ⟨2820608798903035392087625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60172987709931421697869333 2820608798903035392087625)
                      ·
                        rfl

theorem cell23_5493116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_5493116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493116 prefixEnd_5493116 := by exact prefixLift 5493116
  have htrace : WordTrace (prefixWord ++ tailWord_5493116) baseStart_5493116 baseEnd_5493116 := by
    simpa [prefixWord, tailWord_5493116, baseEnd_5493116] using wordTrace_append hprefix tailTrace_5493116
  have hstable : (prefixWord ++ tailWord_5493116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493116).length < 2 ^ (prefixWord ++ tailWord_5493116).sum := by decide
  have hdescent : baseEnd_5493116 < baseStart_5493116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493134 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_5493134 : Nat := 118140960795 + 5493134 * 2 ^ 59
def prefixEnd_5493134 : Nat := 4983230072969 + 3 ^ 40 * 5493134 * 2
def baseEnd_5493134 : Nat := 940206013851605440554181

theorem tailTrace_5493134 : CollatzResearch.WordTrace tailWord_5493134 prefixEnd_5493134 940206013851605440554181 := by
  unfold tailWord_5493134
  simp only [CollatzResearch.WordTrace]
  refine ⟨25043882060165143180270807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133567370987547430294777637 25043882060165143180270807)
  ·
    refine ⟨37565823090247714770406211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25043882060165143180270807 37565823090247714770406211)
    ·
      refine ⟨56348734635371572155609317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37565823090247714770406211 56348734635371572155609317)
      ·
        refine ⟨10565387744132169779176747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56348734635371572155609317 10565387744132169779176747)
        ·
          refine ⟨15848081616198254668765121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10565387744132169779176747 15848081616198254668765121)
          ·
            refine ⟨11886061212148691001573841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15848081616198254668765121 11886061212148691001573841)
            ·
              refine ⟨8914545909111518251180381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11886061212148691001573841 8914545909111518251180381)
              ·
                refine ⟨3342954715916819344192643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8914545909111518251180381 3342954715916819344192643)
                ·
                  refine ⟨5014432073875229016288965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342954715916819344192643 5014432073875229016288965)
                  ·
                    refine ⟨940206013851605440554181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014432073875229016288965 940206013851605440554181)
                    ·
                      rfl

theorem cell23_5493134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_5493134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493134 prefixEnd_5493134 := by exact prefixLift 5493134
  have htrace : WordTrace (prefixWord ++ tailWord_5493134) baseStart_5493134 baseEnd_5493134 := by
    simpa [prefixWord, tailWord_5493134, baseEnd_5493134] using wordTrace_append hprefix tailTrace_5493134
  have hstable : (prefixWord ++ tailWord_5493134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493134).length < 2 ^ (prefixWord ++ tailWord_5493134).sum := by decide
  have hdescent : baseEnd_5493134 < baseStart_5493134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493150 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5493150 : Nat := 118140960795 + 5493150 * 2 ^ 59
def prefixEnd_5493150 : Nat := 4983230072969 + 3 ^ 40 * 5493150 * 2
def baseEnd_5493150 : Nat := 2820626257245288259062469

theorem tailTrace_5493150 : CollatzResearch.WordTrace tailWord_5493150 prefixEnd_5493150 2820626257245288259062469 := by
  unfold tailWord_5493150
  simp only [CollatzResearch.WordTrace]
  refine ⟨25043955006157897521843613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133567760032842120116499269 25043955006157897521843613)
  ·
    refine ⟨9391483127309211570691355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25043955006157897521843613 9391483127309211570691355)
    ·
      refine ⟨14087224690963817356037033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391483127309211570691355 14087224690963817356037033)
      ·
        refine ⟨10565418518222863017027775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14087224690963817356037033 10565418518222863017027775)
        ·
          refine ⟨15848127777334294525541663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10565418518222863017027775 15848127777334294525541663)
          ·
            refine ⟨23772191666001441788312495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15848127777334294525541663 23772191666001441788312495)
            ·
              refine ⟨35658287499002162682468743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23772191666001441788312495 35658287499002162682468743)
              ·
                refine ⟨53487431248503244023703115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35658287499002162682468743 53487431248503244023703115)
                ·
                  refine ⟨80231146872754866035554673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53487431248503244023703115 80231146872754866035554673)
                  ·
                    refine ⟨60173360154566149526666005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80231146872754866035554673 60173360154566149526666005)
                    ·
                      refine ⟨2820626257245288259062469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60173360154566149526666005 2820626257245288259062469)
                      ·
                        rfl

theorem cell23_5493150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5493150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493150 prefixEnd_5493150 := by exact prefixLift 5493150
  have htrace : WordTrace (prefixWord ++ tailWord_5493150) baseStart_5493150 baseEnd_5493150 := by
    simpa [prefixWord, tailWord_5493150, baseEnd_5493150] using wordTrace_append hprefix tailTrace_5493150
  have hstable : (prefixWord ++ tailWord_5493150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493150).length < 2 ^ (prefixWord ++ tailWord_5493150).sum := by decide
  have hdescent : baseEnd_5493150 < baseStart_5493150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493157 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 1, 1, 3]
def baseStart_5493157 : Nat := 118140960795 + 5493157 * 2 ^ 59
def prefixEnd_5493157 : Nat := 4983230072969 + 3 ^ 40 * 5493157 * 2
def baseEnd_5493157 : Nat := 2820629851609869731674937

theorem tailTrace_5493157 : CollatzResearch.WordTrace tailWord_5493157 prefixEnd_5493157 2820629851609869731674937 := by
  unfold tailWord_5493157
  simp only [CollatzResearch.WordTrace]
  refine ⟨200351895360237820370253725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133567930240158546913502483 200351895360237820370253725)
  ·
    refine ⟨75131960760089182638845147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200351895360237820370253725 75131960760089182638845147)
    ·
      refine ⟨112697941140133773958267721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75131960760089182638845147 112697941140133773958267721)
      ·
        refine ⟨84523455855100330468700791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112697941140133773958267721 84523455855100330468700791)
        ·
          refine ⟨126785183782650495703051187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84523455855100330468700791 126785183782650495703051187)
          ·
            refine ⟨190177775673975743554576781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126785183782650495703051187 190177775673975743554576781)
            ·
              refine ⟨71316665877740903832966293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190177775673975743554576781 71316665877740903832966293)
              ·
                refine ⟨3342968713019104867170295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71316665877740903832966293 3342968713019104867170295)
                ·
                  refine ⟨5014453069528657300755443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342968713019104867170295 5014453069528657300755443)
                  ·
                    refine ⟨7521679604292985951133165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5014453069528657300755443 7521679604292985951133165)
                    ·
                      refine ⟨2820629851609869731674937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7521679604292985951133165 2820629851609869731674937)
                      ·
                        rfl

theorem cell23_5493157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_5493157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493157 prefixEnd_5493157 := by exact prefixLift 5493157
  have htrace : WordTrace (prefixWord ++ tailWord_5493157) baseStart_5493157 baseEnd_5493157 := by
    simpa [prefixWord, tailWord_5493157, baseEnd_5493157] using wordTrace_append hprefix tailTrace_5493157
  have hstable : (prefixWord ++ tailWord_5493157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493157).length < 2 ^ (prefixWord ++ tailWord_5493157).sum := by decide
  have hdescent : baseEnd_5493157 < baseStart_5493157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493185 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5493185 : Nat := 118140960795 + 5493185 * 2 ^ 59
def prefixEnd_5493185 : Nat := 4983230072969 + 3 ^ 40 * 5493185 * 2
def baseEnd_5493185 : Nat := 940214743022731874041603

theorem tailTrace_5493185 : CollatzResearch.WordTrace tailWord_5493185 prefixEnd_5493185 940214743022731874041603 := by
  unfold tailWord_5493185
  simp only [CollatzResearch.WordTrace]
  refine ⟨200352916604136381152273009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133568611069424254101515339 200352916604136381152273009)
  ·
    refine ⟨150264687453102285864204757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200352916604136381152273009 150264687453102285864204757)
    ·
      refine ⟨3521828612182084824942299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 150264687453102285864204757 3521828612182084824942299)
      ·
        refine ⟨5282742918273127237413449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521828612182084824942299 5282742918273127237413449)
        ·
          refine ⟨3962057188704845428060087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282742918273127237413449 3962057188704845428060087)
          ·
            refine ⟨5943085783057268142090131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962057188704845428060087 5943085783057268142090131)
            ·
              refine ⟨8914628674585902213135197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943085783057268142090131 8914628674585902213135197)
              ·
                refine ⟨3342985752969713329925699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8914628674585902213135197 3342985752969713329925699)
                ·
                  refine ⟨5014478629454569994888549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342985752969713329925699 5014478629454569994888549)
                  ·
                    refine ⟨940214743022731874041603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014478629454569994888549 940214743022731874041603)
                    ·
                      rfl

theorem cell23_5493185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5493185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493185 prefixEnd_5493185 := by exact prefixLift 5493185
  have htrace : WordTrace (prefixWord ++ tailWord_5493185) baseStart_5493185 baseEnd_5493185 := by
    simpa [prefixWord, tailWord_5493185, baseEnd_5493185] using wordTrace_append hprefix tailTrace_5493185
  have hstable : (prefixWord ++ tailWord_5493185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493185).length < 2 ^ (prefixWord ++ tailWord_5493185).sum := by decide
  have hdescent : baseEnd_5493185 < baseStart_5493185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493193 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_5493193 : Nat := 118140960795 + 5493193 * 2 ^ 59
def prefixEnd_5493193 : Nat := 4983230072969 + 3 ^ 40 * 5493193 * 2
def baseEnd_5493193 : Nat := 2820648336913431590824771

theorem tailTrace_5493193 : CollatzResearch.WordTrace tailWord_5493193 prefixEnd_5493193 2820648336913431590824771 := by
  unfold tailWord_5493193
  simp only [CollatzResearch.WordTrace]
  refine ⟨200353208388107398518564233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133568805592071599012376155 200353208388107398518564233)
  ·
    refine ⟨150264906291080548888923175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200353208388107398518564233 150264906291080548888923175)
    ·
      refine ⟨225397359436620823333384763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150264906291080548888923175 225397359436620823333384763)
      ·
        refine ⟨338096039154931235000077145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225397359436620823333384763 338096039154931235000077145)
        ·
          refine ⟨253572029366198426250057859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338096039154931235000077145 253572029366198426250057859)
          ·
            refine ⟨380358044049297639375086789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253572029366198426250057859 380358044049297639375086789)
            ·
              refine ⟨71317133259243307382828773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 380358044049297639375086789 71317133259243307382828773)
              ·
                refine ⟨13371962486108120134280395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71317133259243307382828773 13371962486108120134280395)
                ·
                  refine ⟨20057943729162180201420593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13371962486108120134280395 20057943729162180201420593)
                  ·
                    refine ⟨15043457796871635151065445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20057943729162180201420593 15043457796871635151065445)
                    ·
                      refine ⟨2820648336913431590824771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15043457796871635151065445 2820648336913431590824771)
                      ·
                        rfl

theorem cell23_5493193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_5493193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493193 prefixEnd_5493193 := by exact prefixLift 5493193
  have htrace : WordTrace (prefixWord ++ tailWord_5493193) baseStart_5493193 baseEnd_5493193 := by
    simpa [prefixWord, tailWord_5493193, baseEnd_5493193] using wordTrace_append hprefix tailTrace_5493193
  have hstable : (prefixWord ++ tailWord_5493193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493193).length < 2 ^ (prefixWord ++ tailWord_5493193).sum := by decide
  have hdescent : baseEnd_5493193 < baseStart_5493193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493223 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5493223 : Nat := 118140960795 + 5493223 * 2 ^ 59
def prefixEnd_5493223 : Nat := 4983230072969 + 3 ^ 40 * 5493223 * 2
def baseEnd_5493223 : Nat := 2820663741333066473449633

theorem tailTrace_5493223 : CollatzResearch.WordTrace tailWord_5493223 prefixEnd_5493223 2820663741333066473449633 := by
  unfold tailWord_5493223
  simp only [CollatzResearch.WordTrace]
  refine ⟨200354302577998713642156323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133569535051999142428104215 200354302577998713642156323)
  ·
    refine ⟨300531453866998070463234485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200354302577998713642156323 300531453866998070463234485)
    ·
      refine ⟨28174823800031069105928233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 300531453866998070463234485 28174823800031069105928233)
      ·
        refine ⟨21131117850023301829446175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28174823800031069105928233 21131117850023301829446175)
        ·
          refine ⟨31696676775034952744169263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21131117850023301829446175 31696676775034952744169263)
          ·
            refine ⟨47545015162552429116253895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31696676775034952744169263 47545015162552429116253895)
            ·
              refine ⟨71317522743828643674380843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47545015162552429116253895 71317522743828643674380843)
              ·
                refine ⟨106976284115742965511571265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71317522743828643674380843 106976284115742965511571265)
                ·
                  refine ⟨80232213086807224133678449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106976284115742965511571265 80232213086807224133678449)
                  ·
                    refine ⟨60174159815105418100258837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80232213086807224133678449 60174159815105418100258837)
                    ·
                      refine ⟨2820663741333066473449633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60174159815105418100258837 2820663741333066473449633)
                      ·
                        rfl

theorem cell23_5493223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5493223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493223 prefixEnd_5493223 := by exact prefixLift 5493223
  have htrace : WordTrace (prefixWord ++ tailWord_5493223) baseStart_5493223 baseEnd_5493223 := by
    simpa [prefixWord, tailWord_5493223, baseEnd_5493223] using wordTrace_append hprefix tailTrace_5493223
  have hstable : (prefixWord ++ tailWord_5493223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493223).length < 2 ^ (prefixWord ++ tailWord_5493223).sum := by decide
  have hdescent : baseEnd_5493223 < baseStart_5493223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493224 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 2, 4]
def baseStart_5493224 : Nat := 118140960795 + 5493224 * 2 ^ 59
def prefixEnd_5493224 : Nat := 4983230072969 + 3 ^ 40 * 5493224 * 2
def baseEnd_5493224 : Nat := 940221418271240323179043

theorem tailTrace_5493224 : CollatzResearch.WordTrace tailWord_5493224 prefixEnd_5493224 940221418271240323179043 := by
  unfold tailWord_5493224
  simp only [CollatzResearch.WordTrace]
  refine ⟨100177169525497545406471363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133569559367330060541961817 100177169525497545406471363)
  ·
    refine ⟨150265754288246318109707045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100177169525497545406471363 150265754288246318109707045)
    ·
      refine ⟨28174828929046184645570071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150265754288246318109707045 28174828929046184645570071)
      ·
        refine ⟨42262243393569276968355107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28174828929046184645570071 42262243393569276968355107)
        ·
          refine ⟨63393365090353915452532661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42262243393569276968355107 63393365090353915452532661)
          ·
            refine ⟨5943127977220679573674937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63393365090353915452532661 5943127977220679573674937)
            ·
              refine ⟨4457345982915509680256203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943127977220679573674937 4457345982915509680256203)
              ·
                refine ⟨6686018974373264520384305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457345982915509680256203 6686018974373264520384305)
                ·
                  refine ⟨5014514230779948390288229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686018974373264520384305 5014514230779948390288229)
                  ·
                    refine ⟨940221418271240323179043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014514230779948390288229 940221418271240323179043)
                    ·
                      rfl

theorem cell23_5493224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_5493224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493224 prefixEnd_5493224 := by exact prefixLift 5493224
  have htrace : WordTrace (prefixWord ++ tailWord_5493224) baseStart_5493224 baseEnd_5493224 := by
    simpa [prefixWord, tailWord_5493224, baseEnd_5493224] using wordTrace_append hprefix tailTrace_5493224
  have hstable : (prefixWord ++ tailWord_5493224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493224).length < 2 ^ (prefixWord ++ tailWord_5493224).sum := by decide
  have hdescent : baseEnd_5493224 < baseStart_5493224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493353 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_5493353 : Nat := 118140960795 + 5493353 * 2 ^ 59
def prefixEnd_5493353 : Nat := 4983230072969 + 3 ^ 40 * 5493353 * 2
def baseEnd_5493353 : Nat := 940243497939383654941345

theorem tailTrace_5493353 : CollatzResearch.WordTrace tailWord_5493353 prefixEnd_5493353 940243497939383654941345 := by
  unfold tailWord_5493353
  simp only [CollatzResearch.WordTrace]
  refine ⟨200359044067527745844388713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133572696045018497229592475 200359044067527745844388713)
  ·
    refine ⟨150269283050645809383291535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200359044067527745844388713 150269283050645809383291535)
    ·
      refine ⟨225403924575968714074937303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150269283050645809383291535 225403924575968714074937303)
      ·
        refine ⟨338105886863953071112405955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225403924575968714074937303 338105886863953071112405955)
        ·
          refine ⟨507158830295929606668608933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338105886863953071112405955 507158830295929606668608933)
          ·
            refine ⟨95092280680486801250364175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 507158830295929606668608933 95092280680486801250364175)
            ·
              refine ⟨142638421020730201875546263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95092280680486801250364175 142638421020730201875546263)
              ·
                refine ⟨213957631531095302813319395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142638421020730201875546263 213957631531095302813319395)
                ·
                  refine ⟨320936447296642954219979093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213957631531095302813319395 320936447296642954219979093)
                  ·
                    refine ⟨940243497939383654941345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 320936447296642954219979093 940243497939383654941345)
                    ·
                      rfl

theorem cell23_5493353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_5493353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493353 prefixEnd_5493353 := by exact prefixLift 5493353
  have htrace : WordTrace (prefixWord ++ tailWord_5493353) baseStart_5493353 baseEnd_5493353 := by
    simpa [prefixWord, tailWord_5493353, baseEnd_5493353] using wordTrace_append hprefix tailTrace_5493353
  have hstable : (prefixWord ++ tailWord_5493353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493353).length < 2 ^ (prefixWord ++ tailWord_5493353).sum := by decide
  have hdescent : baseEnd_5493353 < baseStart_5493353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493377 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5493377 : Nat := 118140960795 + 5493377 * 2 ^ 59
def prefixEnd_5493377 : Nat := 4983230072969 + 3 ^ 40 * 5493377 * 2
def baseEnd_5493377 : Nat := 2820742817353858870923925

theorem tailTrace_5493377 : CollatzResearch.WordTrace tailWord_5493377 prefixEnd_5493377 2820742817353858870923925 := by
  unfold tailWord_5493377
  simp only [CollatzResearch.WordTrace]
  refine ⟨200359919419440797943262385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133573279612960531962174923 200359919419440797943262385)
  ·
    refine ⟨150269939564580598457446789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200359919419440797943262385 150269939564580598457446789)
    ·
      refine ⟨28175613668358862210771273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150269939564580598457446789 28175613668358862210771273)
      ·
        refine ⟨21131710251269146658078455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28175613668358862210771273 21131710251269146658078455)
        ·
          refine ⟨31697565376903719987117683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21131710251269146658078455 31697565376903719987117683)
          ·
            refine ⟨47546348065355579980676525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31697565376903719987117683 47546348065355579980676525)
            ·
              refine ⟨17829880524508342492753697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47546348065355579980676525 17829880524508342492753697)
              ·
                refine ⟨13372410393381256869565273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17829880524508342492753697 13372410393381256869565273)
                ·
                  refine ⟨10029307795035942652173955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13372410393381256869565273 10029307795035942652173955)
                  ·
                    refine ⟨15043961692553913978260933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10029307795035942652173955 15043961692553913978260933)
                    ·
                      refine ⟨2820742817353858870923925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15043961692553913978260933 2820742817353858870923925)
                      ·
                        rfl

theorem cell23_5493377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5493377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493377 prefixEnd_5493377 := by exact prefixLift 5493377
  have htrace : WordTrace (prefixWord ++ tailWord_5493377) baseStart_5493377 baseEnd_5493377 := by
    simpa [prefixWord, tailWord_5493377, baseEnd_5493377] using wordTrace_append hprefix tailTrace_5493377
  have hstable : (prefixWord ++ tailWord_5493377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493377).length < 2 ^ (prefixWord ++ tailWord_5493377).sum := by decide
  have hdescent : baseEnd_5493377 < baseStart_5493377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493378 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_5493378 : Nat := 118140960795 + 5493378 * 2 ^ 59
def prefixEnd_5493378 : Nat := 4983230072969 + 3 ^ 40 * 5493378 * 2
def baseEnd_5493378 : Nat := 313415925648279263001269

theorem tailTrace_5493378 : CollatzResearch.WordTrace tailWord_5493378 prefixEnd_5493378 313415925648279263001269 := by
  unfold tailWord_5493378
  simp only [CollatzResearch.WordTrace]
  refine ⟨50089988973109293778512197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133573303928291450076032525 50089988973109293778512197)
  ·
    refine ⟨9391872932457992583471037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50089988973109293778512197 9391872932457992583471037)
    ·
      refine ⟨3521952349671747218801639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9391872932457992583471037 3521952349671747218801639)
      ·
        refine ⟨5282928524507620828202459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521952349671747218801639 5282928524507620828202459)
        ·
          refine ⟨7924392786761431242303689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282928524507620828202459 7924392786761431242303689)
          ·
            refine ⟨5943294590071073431727767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7924392786761431242303689 5943294590071073431727767)
            ·
              refine ⟨8914941885106610147591651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943294590071073431727767 8914941885106610147591651)
              ·
                refine ⟨13372412827659915221387477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914941885106610147591651 13372412827659915221387477)
                ·
                  refine ⟨313415925648279263001269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13372412827659915221387477 313415925648279263001269)
                  ·
                    rfl

theorem cell23_5493378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_5493378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493378 prefixEnd_5493378 := by exact prefixLift 5493378
  have htrace : WordTrace (prefixWord ++ tailWord_5493378) baseStart_5493378 baseEnd_5493378 := by
    simpa [prefixWord, tailWord_5493378, baseEnd_5493378] using wordTrace_append hprefix tailTrace_5493378
  have hstable : (prefixWord ++ tailWord_5493378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493378).length < 2 ^ (prefixWord ++ tailWord_5493378).sum := by decide
  have hdescent : baseEnd_5493378 < baseStart_5493378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493471 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 2, 3, 2]
def baseStart_5493471 : Nat := 118140960795 + 5493471 * 2 ^ 59
def prefixEnd_5493471 : Nat := 4983230072969 + 3 ^ 40 * 5493471 * 2
def baseEnd_5493471 : Nat := 2820791084535381503148493

theorem tailTrace_5493471 : CollatzResearch.WordTrace tailWord_5493471 prefixEnd_5493471 2820791084535381503148493 := by
  unfold tailWord_5493471
  simp only [CollatzResearch.WordTrace]
  refine ⟨200363347881100251997184267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133575565254066834664789511 200363347881100251997184267)
  ·
    refine ⟨300545021821650377995776401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200363347881100251997184267 300545021821650377995776401)
    ·
      refine ⟨225408766366237783496832301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300545021821650377995776401 225408766366237783496832301)
      ·
        refine ⟨84528287387339168811312113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225408766366237783496832301 84528287387339168811312113)
        ·
          refine ⟨63396215540504376608484085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84528287387339168811312113 63396215540504376608484085)
          ·
            refine ⟨5943395206922285307045383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63396215540504376608484085 5943395206922285307045383)
            ·
              refine ⟨8915092810383427960568075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943395206922285307045383 8915092810383427960568075)
              ·
                refine ⟨13372639215575141940852113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8915092810383427960568075 13372639215575141940852113)
                ·
                  refine ⟨10029479411681356455639085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13372639215575141940852113 10029479411681356455639085)
                  ·
                    refine ⟨3761054779380508670864657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10029479411681356455639085 3761054779380508670864657)
                    ·
                      refine ⟨2820791084535381503148493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761054779380508670864657 2820791084535381503148493)
                      ·
                        rfl

theorem cell23_5493471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_5493471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493471 prefixEnd_5493471 := by exact prefixLift 5493471
  have htrace : WordTrace (prefixWord ++ tailWord_5493471) baseStart_5493471 baseEnd_5493471 := by
    simpa [prefixWord, tailWord_5493471, baseEnd_5493471] using wordTrace_append hprefix tailTrace_5493471
  have hstable : (prefixWord ++ tailWord_5493471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493471).length < 2 ^ (prefixWord ++ tailWord_5493471).sum := by decide
  have hdescent : baseEnd_5493471 < baseStart_5493471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493477 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_5493477 : Nat := 118140960795 + 5493477 * 2 ^ 59
def prefixEnd_5493477 : Nat := 4983230072969 + 3 ^ 40 * 5493477 * 2
def baseEnd_5493477 : Nat := 940264721806436159891155

theorem tailTrace_5493477 : CollatzResearch.WordTrace tailWord_5493477 prefixEnd_5493477 940264721806436159891155 := by
  unfold tailWord_5493477
  simp only [CollatzResearch.WordTrace]
  refine ⟨200363566719078515021902685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133575711146052343347935123 200363566719078515021902685)
  ·
    refine ⟨75136337519654443133213507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200363566719078515021902685 75136337519654443133213507)
    ·
      refine ⟨112704506279481664699820261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75136337519654443133213507 112704506279481664699820261)
      ·
        refine ⟨21132094927402812131216299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112704506279481664699820261 21132094927402812131216299)
        ·
          refine ⟨31698142391104218196824449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21132094927402812131216299 31698142391104218196824449)
          ·
            refine ⟨23773606793328163647618337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31698142391104218196824449 23773606793328163647618337)
            ·
              refine ⟨17830205094996122735713753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23773606793328163647618337 17830205094996122735713753)
              ·
                refine ⟨13372653821247092051785315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17830205094996122735713753 13372653821247092051785315)
                ·
                  refine ⟨20058980731870638077677973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13372653821247092051785315 20058980731870638077677973)
                  ·
                    refine ⟨940264721806436159891155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20058980731870638077677973 940264721806436159891155)
                    ·
                      rfl

theorem cell23_5493477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_5493477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493477 prefixEnd_5493477 := by exact prefixLift 5493477
  have htrace : WordTrace (prefixWord ++ tailWord_5493477) baseStart_5493477 baseEnd_5493477 := by
    simpa [prefixWord, tailWord_5493477, baseEnd_5493477] using wordTrace_append hprefix tailTrace_5493477
  have hstable : (prefixWord ++ tailWord_5493477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493477).length < 2 ^ (prefixWord ++ tailWord_5493477).sum := by decide
  have hdescent : baseEnd_5493477 < baseStart_5493477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493484 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 7, 2, 2]
def baseStart_5493484 : Nat := 118140960795 + 5493484 * 2 ^ 59
def prefixEnd_5493484 : Nat := 4983230072969 + 3 ^ 40 * 5493484 * 2
def baseEnd_5493484 : Nat := 2820797759783889952285933

theorem tailTrace_5493484 : CollatzResearch.WordTrace tailWord_5493484 prefixEnd_5493484 2820797759783889952285933 := by
  unfold tailWord_5493484
  simp only [CollatzResearch.WordTrace]
  refine ⟨100181911015026577608703753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133575881353368770144938337 100181911015026577608703753)
  ·
    refine ⟨75136433261269933206527815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100181911015026577608703753 75136433261269933206527815)
    ·
      refine ⟨112704649891904899809791723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75136433261269933206527815 112704649891904899809791723)
      ·
        refine ⟨169056974837857349714687585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112704649891904899809791723 169056974837857349714687585)
        ·
          refine ⟨126792731128393012286015689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169056974837857349714687585 126792731128393012286015689)
          ·
            refine ⟨95094548346294759214511767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126792731128393012286015689 95094548346294759214511767)
            ·
              refine ⟨142641822519442138821767651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95094548346294759214511767 142641822519442138821767651)
              ·
                refine ⟨213962733779163208232651477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142641822519442138821767651 213962733779163208232651477)
                ·
                  refine ⟨5014751572949137692952769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 213962733779163208232651477 5014751572949137692952769)
                  ·
                    refine ⟨3761063679711853269714577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5014751572949137692952769 3761063679711853269714577)
                    ·
                      refine ⟨2820797759783889952285933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761063679711853269714577 2820797759783889952285933)
                      ·
                        rfl

theorem cell23_5493484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_5493484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493484 prefixEnd_5493484 := by exact prefixLift 5493484
  have htrace : WordTrace (prefixWord ++ tailWord_5493484) baseStart_5493484 baseEnd_5493484 := by
    simpa [prefixWord, tailWord_5493484, baseEnd_5493484] using wordTrace_append hprefix tailTrace_5493484
  have hstable : (prefixWord ++ tailWord_5493484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493484).length < 2 ^ (prefixWord ++ tailWord_5493484).sum := by decide
  have hdescent : baseEnd_5493484 < baseStart_5493484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493494 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_5493494 : Nat := 118140960795 + 5493494 * 2 ^ 59
def prefixEnd_5493494 : Nat := 4983230072969 + 3 ^ 40 * 5493494 * 2
def baseEnd_5493494 : Nat := 940267631530144971053629

theorem tailTrace_5493494 : CollatzResearch.WordTrace tailWord_5493494 prefixEnd_5493494 940267631530144971053629 := by
  unfold tailWord_5493494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522761672501057932829471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133576124506677951283514357 12522761672501057932829471)
  ·
    refine ⟨18784142508751586899244207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12522761672501057932829471 18784142508751586899244207)
    ·
      refine ⟨28176213763127380348866311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18784142508751586899244207 28176213763127380348866311)
      ·
        refine ⟨42264320644691070523299467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28176213763127380348866311 42264320644691070523299467)
        ·
          refine ⟨63396480967036605784949201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42264320644691070523299467 63396480967036605784949201)
          ·
            refine ⟨47547360725277454338711901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63396480967036605784949201 47547360725277454338711901)
            ·
              refine ⟨17830260271979045377016963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47547360725277454338711901 17830260271979045377016963)
              ·
                refine ⟨26745390407968568065525445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17830260271979045377016963 26745390407968568065525445)
                ·
                  refine ⟨5014760701494106512286021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26745390407968568065525445 5014760701494106512286021)
                  ·
                    refine ⟨940267631530144971053629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014760701494106512286021 940267631530144971053629)
                    ·
                      rfl

theorem cell23_5493494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_5493494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493494 prefixEnd_5493494 := by exact prefixLift 5493494
  have htrace : WordTrace (prefixWord ++ tailWord_5493494) baseStart_5493494 baseEnd_5493494 := by
    simpa [prefixWord, tailWord_5493494, baseEnd_5493494] using wordTrace_append hprefix tailTrace_5493494
  have hstable : (prefixWord ++ tailWord_5493494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493494).length < 2 ^ (prefixWord ++ tailWord_5493494).sum := by decide
  have hdescent : baseEnd_5493494 < baseStart_5493494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493501 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_5493501 : Nat := 118140960795 + 5493501 * 2 ^ 59
def prefixEnd_5493501 : Nat := 4983230072969 + 3 ^ 40 * 5493501 * 2
def baseEnd_5493501 : Nat := 2820806488955016385773355

theorem tailTrace_5493501 : CollatzResearch.WordTrace tailWord_5493501 prefixEnd_5493501 2820806488955016385773355 := by
  unfold tailWord_5493501
  simp only [CollatzResearch.WordTrace]
  refine ⟨200364442070991567120776357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133576294713994378080517571 200364442070991567120776357)
  ·
    refine ⟨37568332888310918835145567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200364442070991567120776357 37568332888310918835145567)
    ·
      refine ⟨56352499332466378252718351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37568332888310918835145567 56352499332466378252718351)
      ·
        refine ⟨84528748998699567379077527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56352499332466378252718351 84528748998699567379077527)
        ·
          refine ⟨126793123498049351068616291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84528748998699567379077527 126793123498049351068616291)
          ·
            refine ⟨190189685247074026602924437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126793123498049351068616291 190189685247074026602924437)
            ·
              refine ⟨8915141495956594997012083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190189685247074026602924437 8915141495956594997012083)
              ·
                refine ⟨13372712243934892495518125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8915141495956594997012083 13372712243934892495518125)
                ·
                  refine ⟨5014767091475584685819297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13372712243934892495518125 5014767091475584685819297)
                  ·
                    refine ⟨3761075318606688514364473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5014767091475584685819297 3761075318606688514364473)
                    ·
                      refine ⟨2820806488955016385773355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761075318606688514364473 2820806488955016385773355)
                      ·
                        rfl

theorem cell23_5493501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_5493501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493501 prefixEnd_5493501 := by exact prefixLift 5493501
  have htrace : WordTrace (prefixWord ++ tailWord_5493501) baseStart_5493501 baseEnd_5493501 := by
    simpa [prefixWord, tailWord_5493501, baseEnd_5493501] using wordTrace_append hprefix tailTrace_5493501
  have hstable : (prefixWord ++ tailWord_5493501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493501).length < 2 ^ (prefixWord ++ tailWord_5493501).sum := by decide
  have hdescent : baseEnd_5493501 < baseStart_5493501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493535 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 1, 2, 2]
def baseStart_5493535 : Nat := 118140960795 + 5493535 * 2 ^ 59
def prefixEnd_5493535 : Nat := 4983230072969 + 3 ^ 40 * 5493535 * 2
def baseEnd_5493535 : Nat := 2820823947297269252748199

theorem tailTrace_5493535 : CollatzResearch.WordTrace tailWord_5493535 prefixEnd_5493535 2820823947297269252748199 := by
  unfold tailWord_5493535
  simp only [CollatzResearch.WordTrace]
  refine ⟨200365682152868390927514059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133577121435245593951676039 200365682152868390927514059)
  ·
    refine ⟨300548523229302586391271089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200365682152868390927514059 300548523229302586391271089)
    ·
      refine ⟨225411392421976939793453317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300548523229302586391271089 225411392421976939793453317)
      ·
        refine ⟨42264636079120676211272497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225411392421976939793453317 42264636079120676211272497)
        ·
          refine ⟨31698477059340507158454373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42264636079120676211272497 31698477059340507158454373)
          ·
            refine ⟨5943464448626345092210195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31698477059340507158454373 5943464448626345092210195)
            ·
              refine ⟨8915196672939517638315293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943464448626345092210195 8915196672939517638315293)
              ·
                refine ⟨3343198752352319114368235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8915196672939517638315293 3343198752352319114368235)
                ·
                  refine ⟨5014798128528478671552353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343198752352319114368235 5014798128528478671552353)
                  ·
                    refine ⟨3761098596396359003664265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5014798128528478671552353 3761098596396359003664265)
                    ·
                      refine ⟨2820823947297269252748199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761098596396359003664265 2820823947297269252748199)
                      ·
                        rfl

theorem cell23_5493535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_5493535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493535 prefixEnd_5493535 := by exact prefixLift 5493535
  have htrace : WordTrace (prefixWord ++ tailWord_5493535) baseStart_5493535 baseEnd_5493535 := by
    simpa [prefixWord, tailWord_5493535, baseEnd_5493535] using wordTrace_append hprefix tailTrace_5493535
  have hstable : (prefixWord ++ tailWord_5493535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493535).length < 2 ^ (prefixWord ++ tailWord_5493535).sum := by decide
  have hdescent : baseEnd_5493535 < baseStart_5493535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493572 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5493572 : Nat := 118140960795 + 5493572 * 2 ^ 59
def prefixEnd_5493572 : Nat := 4983230072969 + 3 ^ 40 * 5493572 * 2
def baseEnd_5493572 : Nat := 2820842946081485607985529

theorem tailTrace_5493572 : CollatzResearch.WordTrace tailWord_5493572 prefixEnd_5493572 2820842946081485607985529 := by
  unfold tailWord_5493572
  simp only [CollatzResearch.WordTrace]
  refine ⟨100183515826867173123305485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133578021102489564164407313 100183515826867173123305485)
  ·
    refine ⟨37568818435075189921239557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100183515826867173123305485 37568818435075189921239557)
    ·
      refine ⟨7044153456576598110232417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37568818435075189921239557 7044153456576598110232417)
      ·
        refine ⟨5283115092432448582674313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7044153456576598110232417 5283115092432448582674313)
        ·
          refine ⟨3962336319324336437005735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5283115092432448582674313 3962336319324336437005735)
          ·
            refine ⟨5943504478986504655508603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962336319324336437005735 5943504478986504655508603)
            ·
              refine ⟨8915256718479756983262905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943504478986504655508603 8915256718479756983262905)
              ·
                refine ⟨6686442538859817737447179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8915256718479756983262905 6686442538859817737447179)
                ·
                  refine ⟨10029663808289726606170769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686442538859817737447179 10029663808289726606170769)
                  ·
                    refine ⟨7522247856217294954628077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10029663808289726606170769 7522247856217294954628077)
                    ·
                      refine ⟨2820842946081485607985529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7522247856217294954628077 2820842946081485607985529)
                      ·
                        rfl

theorem cell23_5493572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5493572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493572 prefixEnd_5493572 := by exact prefixLift 5493572
  have htrace : WordTrace (prefixWord ++ tailWord_5493572) baseStart_5493572 baseEnd_5493572 := by
    simpa [prefixWord, tailWord_5493572, baseEnd_5493572] using wordTrace_append hprefix tailTrace_5493572
  have hstable : (prefixWord ++ tailWord_5493572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493572).length < 2 ^ (prefixWord ++ tailWord_5493572).sum := by decide
  have hdescent : baseEnd_5493572 < baseStart_5493572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493577 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_5493577 : Nat := 118140960795 + 5493577 * 2 ^ 59
def prefixEnd_5493577 : Nat := 4983230072969 + 3 ^ 40 * 5493577 * 2
def baseEnd_5493577 : Nat := 2820845513484758088423005

theorem tailTrace_5493577 : CollatzResearch.WordTrace tailWord_5493577 prefixEnd_5493577 2820845513484758088423005 := by
  unfold tailWord_5493577
  simp only [CollatzResearch.WordTrace]
  refine ⟨200367214018716232100542985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133578142679144154733695323 200367214018716232100542985)
  ·
    refine ⟨150275410514037174075407239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200367214018716232100542985 150275410514037174075407239)
    ·
      refine ⟨225413115771055761113110859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150275410514037174075407239 225413115771055761113110859)
      ·
        refine ⟨338119673656583641669666289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225413115771055761113110859 338119673656583641669666289)
        ·
          refine ⟨253589755242437731252249717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338119673656583641669666289 253589755242437731252249717)
          ·
            refine ⟨23774039553978537304898411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 253589755242437731252249717 23774039553978537304898411)
            ·
              refine ⟨35661059330967805957347617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23774039553978537304898411 35661059330967805957347617)
              ·
                refine ⟨26745794498225854468010713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35661059330967805957347617 26745794498225854468010713)
                ·
                  refine ⟨20059345873669390851008035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26745794498225854468010713 20059345873669390851008035)
                  ·
                    refine ⟨30089018810504086276512053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20059345873669390851008035 30089018810504086276512053)
                    ·
                      refine ⟨2820845513484758088423005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30089018810504086276512053 2820845513484758088423005)
                      ·
                        rfl

theorem cell23_5493577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_5493577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493577 prefixEnd_5493577 := by exact prefixLift 5493577
  have htrace : WordTrace (prefixWord ++ tailWord_5493577) baseStart_5493577 baseEnd_5493577 := by
    simpa [prefixWord, tailWord_5493577, baseEnd_5493577] using wordTrace_append hprefix tailTrace_5493577
  have hstable : (prefixWord ++ tailWord_5493577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493577).length < 2 ^ (prefixWord ++ tailWord_5493577).sum := by decide
  have hdescent : baseEnd_5493577 < baseStart_5493577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493591 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 1, 4, 2]
def baseStart_5493591 : Nat := 118140960795 + 5493591 * 2 ^ 59
def prefixEnd_5493591 : Nat := 4983230072969 + 3 ^ 40 * 5493591 * 2
def baseEnd_5493591 : Nat := 2820852702213921033647941

theorem tailTrace_5493591 : CollatzResearch.WordTrace tailWord_5493591 prefixEnd_5493591 2820852702213921033647941 := by
  unfold tailWord_5493591
  simp only [CollatzResearch.WordTrace]
  refine ⟨200367724640665512491552627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133578483093777008327701751 200367724640665512491552627)
  ·
    refine ⟨300551586960998268737328941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200367724640665512491552627 300551586960998268737328941)
    ·
      refine ⟨112706845110374350776498353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300551586960998268737328941 112706845110374350776498353)
      ·
        refine ⟨84530133832780763082373765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112706845110374350776498353 84530133832780763082373765)
        ·
          refine ⟨15849400093646393077945081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84530133832780763082373765 15849400093646393077945081)
          ·
            refine ⟨11887050070234794808458811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15849400093646393077945081 11887050070234794808458811)
            ·
              refine ⟨17830575105352192212688217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11887050070234794808458811 17830575105352192212688217)
              ·
                refine ⟨13372931329014144159516163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17830575105352192212688217 13372931329014144159516163)
                ·
                  refine ⟨20059396993521216239274245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13372931329014144159516163 20059396993521216239274245)
                  ·
                    refine ⟨3761136936285228044863921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20059396993521216239274245 3761136936285228044863921)
                    ·
                      refine ⟨2820852702213921033647941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761136936285228044863921 2820852702213921033647941)
                      ·
                        rfl

theorem cell23_5493591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_5493591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493591 prefixEnd_5493591 := by exact prefixLift 5493591
  have htrace : WordTrace (prefixWord ++ tailWord_5493591) baseStart_5493591 baseEnd_5493591 := by
    simpa [prefixWord, tailWord_5493591, baseEnd_5493591] using wordTrace_append hprefix tailTrace_5493591
  have hstable : (prefixWord ++ tailWord_5493591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493591).length < 2 ^ (prefixWord ++ tailWord_5493591).sum := by decide
  have hdescent : baseEnd_5493591 < baseStart_5493591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493608 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5493608 : Nat := 118140960795 + 5493608 * 2 ^ 59
def prefixEnd_5493608 : Nat := 4983230072969 + 3 ^ 40 * 5493608 * 2
def baseEnd_5493608 : Nat := 2820861431385047467135363

theorem tailTrace_5493608 : CollatzResearch.WordTrace tailWord_5493608 prefixEnd_5493608 2820861431385047467135363 := by
  unfold tailWord_5493608
  simp only [CollatzResearch.WordTrace]
  refine ⟨100184172340801962197460739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133578896454402616263280985 100184172340801962197460739)
  ·
    refine ⟨150276258511202943296191109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100184172340801962197460739 150276258511202943296191109)
    ·
      refine ⟨28176798470850551868035833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150276258511202943296191109 28176798470850551868035833)
      ·
        refine ⟨21132598853137913901026875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28176798470850551868035833 21132598853137913901026875)
        ·
          refine ⟨31698898279706870851540313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21132598853137913901026875 31698898279706870851540313)
          ·
            refine ⟨23774173709780153138655235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31698898279706870851540313 23774173709780153138655235)
            ·
              refine ⟨35661260564670229707982853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23774173709780153138655235 35661260564670229707982853)
              ·
                refine ⟨6686486355875668070246785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35661260564670229707982853 6686486355875668070246785)
                ·
                  refine ⟨5014864766906751052685089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686486355875668070246785 5014864766906751052685089)
                  ·
                    refine ⟨3761148575180063289513817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5014864766906751052685089 3761148575180063289513817)
                    ·
                      refine ⟨2820861431385047467135363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761148575180063289513817 2820861431385047467135363)
                      ·
                        rfl

theorem cell23_5493608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5493608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493608 prefixEnd_5493608 := by exact prefixLift 5493608
  have htrace : WordTrace (prefixWord ++ tailWord_5493608) baseStart_5493608 baseEnd_5493608 := by
    simpa [prefixWord, tailWord_5493608, baseEnd_5493608] using wordTrace_append hprefix tailTrace_5493608
  have hstable : (prefixWord ++ tailWord_5493608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493608).length < 2 ^ (prefixWord ++ tailWord_5493608).sum := by decide
  have hdescent : baseEnd_5493608 < baseStart_5493608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493627 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 4, 5]
def baseStart_5493627 : Nat := 118140960795 + 5493627 * 2 ^ 59
def prefixEnd_5493627 : Nat := 4983230072969 + 3 ^ 40 * 5493627 * 2
def baseEnd_5493627 : Nat := 940290395839160964265925

theorem tailTrace_5493627 : CollatzResearch.WordTrace tailWord_5493627 prefixEnd_5493627 940290395839160964265925 := by
  unfold tailWord_5493627
  simp only [CollatzResearch.WordTrace]
  refine ⟨200369037668535090639863135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133579358445690060426575423 200369037668535090639863135)
  ·
    refine ⟨300553556502802635959794703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200369037668535090639863135 300553556502802635959794703)
    ·
      refine ⟨450830334754203953939692055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300553556502802635959794703 450830334754203953939692055)
      ·
        refine ⟨676245502131305930909538083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450830334754203953939692055 676245502131305930909538083)
        ·
          refine ⟨1014368253196958896364307125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676245502131305930909538083 1014368253196958896364307125)
          ·
            refine ⟨95097023737214896534153793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1014368253196958896364307125 95097023737214896534153793)
            ·
              refine ⟨71322767802911172400615345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95097023737214896534153793 71322767802911172400615345)
              ·
                refine ⟨53492075852183379300461509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71322767802911172400615345 53492075852183379300461509)
                ·
                  refine ⟨10029764222284383618836533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53492075852183379300461509 10029764222284383618836533)
                  ·
                    refine ⟨940290395839160964265925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10029764222284383618836533 940290395839160964265925)
                    ·
                      rfl

theorem cell23_5493627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 5].length) (baseStart_5493627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493627 prefixEnd_5493627 := by exact prefixLift 5493627
  have htrace : WordTrace (prefixWord ++ tailWord_5493627) baseStart_5493627 baseEnd_5493627 := by
    simpa [prefixWord, tailWord_5493627, baseEnd_5493627] using wordTrace_append hprefix tailTrace_5493627
  have hstable : (prefixWord ++ tailWord_5493627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493627).length < 2 ^ (prefixWord ++ tailWord_5493627).sum := by decide
  have hdescent : baseEnd_5493627 < baseStart_5493627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493644 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_5493644 : Nat := 118140960795 + 5493644 * 2 ^ 59
def prefixEnd_5493644 : Nat := 4983230072969 + 3 ^ 40 * 5493644 * 2
def baseEnd_5493644 : Nat := 940293305562869775428399

theorem tailTrace_5493644 : CollatzResearch.WordTrace tailWord_5493644 prefixEnd_5493644 940293305562869775428399 := by
  unfold tailWord_5493644
  simp only [CollatzResearch.WordTrace]
  refine ⟨100184828854736751271615993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133579771806315668362154657 100184828854736751271615993)
  ·
    refine ⟨75138621641052563453711995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100184828854736751271615993 75138621641052563453711995)
    ·
      refine ⟨112707932461578845180567993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75138621641052563453711995 112707932461578845180567993)
      ·
        refine ⟨84530949346184133885425995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112707932461578845180567993 84530949346184133885425995)
        ·
          refine ⟨126796424019276200828138993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84530949346184133885425995 126796424019276200828138993)
          ·
            refine ⟨95097318014457150621104245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126796424019276200828138993 95097318014457150621104245)
            ·
              refine ⟨8915373563855357870728523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95097318014457150621104245 8915373563855357870728523)
              ·
                refine ⟨13373060345783036806092785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8915373563855357870728523 13373060345783036806092785)
                ·
                  refine ⟨10029795259337277604569589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13373060345783036806092785 10029795259337277604569589)
                  ·
                    refine ⟨940293305562869775428399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10029795259337277604569589 940293305562869775428399)
                    ·
                      rfl

theorem cell23_5493644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_5493644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493644 prefixEnd_5493644 := by exact prefixLift 5493644
  have htrace : WordTrace (prefixWord ++ tailWord_5493644) baseStart_5493644 baseEnd_5493644 := by
    simpa [prefixWord, tailWord_5493644, baseEnd_5493644] using wordTrace_append hprefix tailTrace_5493644
  have hstable : (prefixWord ++ tailWord_5493644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493644).length < 2 ^ (prefixWord ++ tailWord_5493644).sum := by decide
  have hdescent : baseEnd_5493644 < baseStart_5493644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493664 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5493664 : Nat := 118140960795 + 5493664 * 2 ^ 59
def prefixEnd_5493664 : Nat := 4983230072969 + 3 ^ 40 * 5493664 * 2
def baseEnd_5493664 : Nat := 2820890186301699248035105

theorem tailTrace_5493664 : CollatzResearch.WordTrace tailWord_5493664 prefixEnd_5493664 2820890186301699248035105 := by
  unfold tailWord_5493664
  simp only [CollatzResearch.WordTrace]
  refine ⟨100185193584700522979480023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133580258112934030639306697 100185193584700522979480023)
  ·
    refine ⟨150277790377050784469220035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100185193584700522979480023 150277790377050784469220035)
    ·
      refine ⟨225416685565576176703830053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150277790377050784469220035 225416685565576176703830053)
      ·
        refine ⟨42265628543545533131968135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225416685565576176703830053 42265628543545533131968135)
        ·
          refine ⟨63398442815318299697952203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42265628543545533131968135 63398442815318299697952203)
          ·
            refine ⟨95097664222977449546928305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63398442815318299697952203 95097664222977449546928305)
            ·
              refine ⟨71323248167233087160196229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95097664222977449546928305 71323248167233087160196229)
              ·
                refine ⟨13373109031356203842536793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71323248167233087160196229 13373109031356203842536793)
                ·
                  refine ⟨10029831773517152881902595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13373109031356203842536793 10029831773517152881902595)
                  ·
                    refine ⟨15044747660275729322853893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10029831773517152881902595 15044747660275729322853893)
                    ·
                      refine ⟨2820890186301699248035105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15044747660275729322853893 2820890186301699248035105)
                      ·
                        rfl

theorem cell23_5493664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5493664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493664 prefixEnd_5493664 := by exact prefixLift 5493664
  have htrace : WordTrace (prefixWord ++ tailWord_5493664) baseStart_5493664 baseEnd_5493664 := by
    simpa [prefixWord, tailWord_5493664, baseEnd_5493664] using wordTrace_append hprefix tailTrace_5493664
  have hstable : (prefixWord ++ tailWord_5493664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493664).length < 2 ^ (prefixWord ++ tailWord_5493664).sum := by decide
  have hdescent : baseEnd_5493664 < baseStart_5493664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493667 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_5493667 : Nat := 118140960795 + 5493667 * 2 ^ 59
def prefixEnd_5493667 : Nat := 4983230072969 + 3 ^ 40 * 5493667 * 2
def baseEnd_5493667 : Nat := 2820891726743662736297591

theorem tailTrace_5493667 : CollatzResearch.WordTrace tailWord_5493667 prefixEnd_5493667 2820891726743662736297591 := by
  unfold tailWord_5493667
  simp only [CollatzResearch.WordTrace]
  refine ⟨200370496588390177471319255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133580331058926784980879503 200370496588390177471319255)
  ·
    refine ⟨300555744882585266206978883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200370496588390177471319255 300555744882585266206978883)
    ·
      refine ⟨450833617323877899310468325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300555744882585266206978883 450833617323877899310468325)
      ·
        refine ⟨84531303248227106120712811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 450833617323877899310468325 84531303248227106120712811)
        ·
          refine ⟨126796954872340659181069217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84531303248227106120712811 126796954872340659181069217)
          ·
            refine ⟨95097716154255494385801913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126796954872340659181069217 95097716154255494385801913)
            ·
              refine ⟨71323287115691620789351435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95097716154255494385801913 71323287115691620789351435)
              ·
                refine ⟨106984930673537431184027153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71323287115691620789351435 106984930673537431184027153)
                ·
                  refine ⟨80238698005153073388020365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106984930673537431184027153 80238698005153073388020365)
                  ·
                    refine ⟨30089511751932402520507637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80238698005153073388020365 30089511751932402520507637)
                    ·
                      refine ⟨2820891726743662736297591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30089511751932402520507637 2820891726743662736297591)
                      ·
                        rfl

theorem cell23_5493667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_5493667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493667 prefixEnd_5493667 := by exact prefixLift 5493667
  have htrace : WordTrace (prefixWord ++ tailWord_5493667) baseStart_5493667 baseEnd_5493667 := by
    simpa [prefixWord, tailWord_5493667, baseEnd_5493667] using wordTrace_append hprefix tailTrace_5493667
  have hstable : (prefixWord ++ tailWord_5493667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493667).length < 2 ^ (prefixWord ++ tailWord_5493667).sum := by decide
  have hdescent : baseEnd_5493667 < baseStart_5493667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493694 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5493694 : Nat := 118140960795 + 5493694 * 2 ^ 59
def prefixEnd_5493694 : Nat := 4983230072969 + 3 ^ 40 * 5493694 * 2
def baseEnd_5493694 : Nat := 2820905590721334130659967

theorem tailTrace_5493694 : CollatzResearch.WordTrace tailWord_5493694 prefixEnd_5493694 2820905590721334130659967 := by
  unfold tailWord_5493694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25046435169911545135319017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133580987572861574055034757 25046435169911545135319017)
  ·
    refine ⟨18784826377433658851489263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25046435169911545135319017 18784826377433658851489263)
    ·
      refine ⟨28177239566150488277233895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18784826377433658851489263 28177239566150488277233895)
      ·
        refine ⟨42265859349225732415850843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28177239566150488277233895 42265859349225732415850843)
        ·
          refine ⟨63398789023838598623776265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42265859349225732415850843 63398789023838598623776265)
          ·
            refine ⟨47549091767878948967832199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63398789023838598623776265 47549091767878948967832199)
            ·
              refine ⟨71323637651818423451748299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47549091767878948967832199 71323637651818423451748299)
              ·
                refine ⟨106985456477727635177622449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71323637651818423451748299 106985456477727635177622449)
                ·
                  refine ⟨80239092358295726383216837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106985456477727635177622449 80239092358295726383216837)
                  ·
                    refine ⟨15044829817180448696853157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80239092358295726383216837 15044829817180448696853157)
                    ·
                      refine ⟨2820905590721334130659967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15044829817180448696853157 2820905590721334130659967)
                      ·
                        rfl

theorem cell23_5493694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5493694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493694 prefixEnd_5493694 := by exact prefixLift 5493694
  have htrace : WordTrace (prefixWord ++ tailWord_5493694) baseStart_5493694 baseEnd_5493694 := by
    simpa [prefixWord, tailWord_5493694, baseEnd_5493694] using wordTrace_append hprefix tailTrace_5493694
  have hstable : (prefixWord ++ tailWord_5493694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493694).length < 2 ^ (prefixWord ++ tailWord_5493694).sum := by decide
  have hdescent : baseEnd_5493694 < baseStart_5493694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493718 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_5493718 : Nat := 118140960795 + 5493718 * 2 ^ 59
def prefixEnd_5493718 : Nat := 4983230072969 + 3 ^ 40 * 5493718 * 2
def baseEnd_5493718 : Nat := 2820917914257042036759857

theorem tailTrace_5493718 : CollatzResearch.WordTrace tailWord_5493718 prefixEnd_5493718 2820917914257042036759857 := by
  unfold tailWord_5493718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12523272294450338323839113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133581571140803608787617205 12523272294450338323839113)
  ·
    refine ⟨9392454220837753742879335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12523272294450338323839113 9392454220837753742879335)
    ·
      refine ⟨14088681331256630614319003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9392454220837753742879335 14088681331256630614319003)
      ·
        refine ⟨21133021996884945921478505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14088681331256630614319003 21133021996884945921478505)
        ·
          refine ⟨15849766497663709441108879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21133021996884945921478505 15849766497663709441108879)
          ·
            refine ⟨23774649746495564161663319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15849766497663709441108879 23774649746495564161663319)
            ·
              refine ⟨35661974619743346242494979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23774649746495564161663319 35661974619743346242494979)
              ·
                refine ⟨53492961929615019363742469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35661974619743346242494979 53492961929615019363742469)
                ·
                  refine ⟨10029930361802816130701713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53492961929615019363742469 10029930361802816130701713)
                  ·
                    refine ⟨7522447771352112098026285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10029930361802816130701713 7522447771352112098026285)
                    ·
                      refine ⟨2820917914257042036759857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7522447771352112098026285 2820917914257042036759857)
                      ·
                        rfl

theorem cell23_5493718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_5493718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493718 prefixEnd_5493718 := by exact prefixLift 5493718
  have htrace : WordTrace (prefixWord ++ tailWord_5493718) baseStart_5493718 baseEnd_5493718 := by
    simpa [prefixWord, tailWord_5493718, baseEnd_5493718] using wordTrace_append hprefix tailTrace_5493718
  have hstable : (prefixWord ++ tailWord_5493718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493718).length < 2 ^ (prefixWord ++ tailWord_5493718).sum := by decide
  have hdescent : baseEnd_5493718 < baseStart_5493718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493737 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_5493737 : Nat := 118140960795 + 5493737 * 2 ^ 59
def prefixEnd_5493737 : Nat := 4983230072969 + 3 ^ 40 * 5493737 * 2
def baseEnd_5493737 : Nat := 2820927670389477462422269

theorem tailTrace_5493737 : CollatzResearch.WordTrace tailWord_5493737 prefixEnd_5493737 2820927670389477462422269 := by
  unfold tailWord_5493737
  simp only [CollatzResearch.WordTrace]
  refine ⟨200373049698136579426367465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133582033132091052950911643 200373049698136579426367465)
  ·
    refine ⟨150279787273602434569775599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200373049698136579426367465 150279787273602434569775599)
    ·
      refine ⟨225419680910403651854663399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150279787273602434569775599 225419680910403651854663399)
      ·
        refine ⟨338129521365605477781995099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225419680910403651854663399 338129521365605477781995099)
        ·
          refine ⟨507194282048408216672992649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338129521365605477781995099 507194282048408216672992649)
          ·
            refine ⟨380395711536306162504744487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507194282048408216672992649 380395711536306162504744487)
            ·
              refine ⟨570593567304459243757116731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380395711536306162504744487 570593567304459243757116731)
              ·
                refine ⟨855890350956688865635675097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570593567304459243757116731 855890350956688865635675097)
                ·
                  refine ⟨641917763217516649226756323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 855890350956688865635675097 641917763217516649226756323)
                  ·
                    refine ⟨962876644826274973840134485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 641917763217516649226756323 962876644826274973840134485)
                    ·
                      refine ⟨2820927670389477462422269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 962876644826274973840134485 2820927670389477462422269)
                      ·
                        rfl

theorem cell23_5493737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_5493737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493737 prefixEnd_5493737 := by exact prefixLift 5493737
  have htrace : WordTrace (prefixWord ++ tailWord_5493737) baseStart_5493737 baseEnd_5493737 := by
    simpa [prefixWord, tailWord_5493737, baseEnd_5493737] using wordTrace_append hprefix tailTrace_5493737
  have hstable : (prefixWord ++ tailWord_5493737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493737).length < 2 ^ (prefixWord ++ tailWord_5493737).sum := by decide
  have hdescent : baseEnd_5493737 < baseStart_5493737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493738 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_5493738 : Nat := 118140960795 + 5493738 * 2 ^ 59
def prefixEnd_5493738 : Nat := 4983230072969 + 3 ^ 40 * 5493738 * 2
def baseEnd_5493738 : Nat := 313436464874459106501085

theorem tailTrace_5493738 : CollatzResearch.WordTrace tailWord_5493738 prefixEnd_5493738 313436464874459106501085 := by
  unfold tailWord_5493738
  simp only [CollatzResearch.WordTrace]
  refine ⟨50093271542783239149288467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133582057447421971064769245 50093271542783239149288467)
  ·
    refine ⟨75139907314174858723932701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50093271542783239149288467 75139907314174858723932701)
    ·
      refine ⟨28177465242815572021474763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75139907314174858723932701 28177465242815572021474763)
      ·
        refine ⟨42266197864223358032212145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28177465242815572021474763 42266197864223358032212145)
        ·
          refine ⟨31699648398167518524159109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42266197864223358032212145 31699648398167518524159109)
          ·
            refine ⟨5943684074656409723279833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31699648398167518524159109 5943684074656409723279833)
            ·
              refine ⟨4457763055992307292459875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943684074656409723279833 4457763055992307292459875)
              ·
                refine ⟨6686644583988460938689813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457763055992307292459875 6686644583988460938689813)
                ·
                  refine ⟨313436464874459106501085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6686644583988460938689813 313436464874459106501085)
                  ·
                    rfl

theorem cell23_5493738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_5493738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493738 prefixEnd_5493738 := by exact prefixLift 5493738
  have htrace : WordTrace (prefixWord ++ tailWord_5493738) baseStart_5493738 baseEnd_5493738 := by
    simpa [prefixWord, tailWord_5493738, baseEnd_5493738] using wordTrace_append hprefix tailTrace_5493738
  have hstable : (prefixWord ++ tailWord_5493738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493738).length < 2 ^ (prefixWord ++ tailWord_5493738).sum := by decide
  have hdescent : baseEnd_5493738 < baseStart_5493738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493768 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 1, 5]
def baseStart_5493768 : Nat := 118140960795 + 5493768 * 2 ^ 59
def prefixEnd_5493768 : Nat := 4983230072969 + 3 ^ 40 * 5493768 * 2
def baseEnd_5493768 : Nat := 940314529429922280378209

theorem tailTrace_5493768 : CollatzResearch.WordTrace tailWord_5493768 prefixEnd_5493768 940314529429922280378209 := by
  unfold tailWord_5493768
  simp only [CollatzResearch.WordTrace]
  refine ⟨100187090180512135860372979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133582786907349514480497305 100187090180512135860372979)
  ·
    refine ⟨150280635270768203790559469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100187090180512135860372979 150280635270768203790559469)
    ·
      refine ⟨56355238226538076421459801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150280635270768203790559469 56355238226538076421459801)
      ·
        refine ⟨42266428669903557316094851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56355238226538076421459801 42266428669903557316094851)
        ·
          refine ⟨63399643004855335974142277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42266428669903557316094851 63399643004855335974142277)
          ·
            refine ⟨11887433063410375495151677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63399643004855335974142277 11887433063410375495151677)
            ·
              refine ⟨4457787398778890810681879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11887433063410375495151677 4457787398778890810681879)
              ·
                refine ⟨6686681098168336216022819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457787398778890810681879 6686681098168336216022819)
                ·
                  refine ⟨10030021647252504324034229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686681098168336216022819 10030021647252504324034229)
                  ·
                    refine ⟨940314529429922280378209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10030021647252504324034229 940314529429922280378209)
                    ·
                      rfl

theorem cell23_5493768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_5493768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493768 prefixEnd_5493768 := by exact prefixLift 5493768
  have htrace : WordTrace (prefixWord ++ tailWord_5493768) baseStart_5493768 baseEnd_5493768 := by
    simpa [prefixWord, tailWord_5493768, baseEnd_5493768] using wordTrace_append hprefix tailTrace_5493768
  have hstable : (prefixWord ++ tailWord_5493768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493768).length < 2 ^ (prefixWord ++ tailWord_5493768).sum := by decide
  have hdescent : baseEnd_5493768 < baseStart_5493768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493791 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_5493791 : Nat := 118140960795 + 5493791 * 2 ^ 59
def prefixEnd_5493791 : Nat := 4983230072969 + 3 ^ 40 * 5493791 * 2
def baseEnd_5493791 : Nat := 2820955398344820251147021

theorem tailTrace_5493791 : CollatzResearch.WordTrace tailWord_5493791 prefixEnd_5493791 2820955398344820251147021 := by
  unfold tailWord_5493791
  simp only [CollatzResearch.WordTrace]
  refine ⟨200375019239940946648833227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133583346159960631099222151 200375019239940946648833227)
  ·
    refine ⟨300562528859911419973249841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200375019239940946648833227 300562528859911419973249841)
    ·
      refine ⟨225421896644933564979937381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300562528859911419973249841 225421896644933564979937381)
      ·
        refine ⟨42266605620925043433738259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225421896644933564979937381 42266605620925043433738259)
        ·
          refine ⟨63399908431387565150607389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42266605620925043433738259 63399908431387565150607389)
          ·
            refine ⟨23774965661770336931477771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63399908431387565150607389 23774965661770336931477771)
            ·
              refine ⟨35662448492655505397216657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23774965661770336931477771 35662448492655505397216657)
              ·
                refine ⟨26746836369491629047912493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35662448492655505397216657 26746836369491629047912493)
                ·
                  refine ⟨10030063638559360892967185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26746836369491629047912493 10030063638559360892967185)
                  ·
                    refine ⟨7522547728919520669725389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10030063638559360892967185 7522547728919520669725389)
                    ·
                      refine ⟨2820955398344820251147021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7522547728919520669725389 2820955398344820251147021)
                      ·
                        rfl

theorem cell23_5493791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_5493791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493791 prefixEnd_5493791 := by exact prefixLift 5493791
  have htrace : WordTrace (prefixWord ++ tailWord_5493791) baseStart_5493791 baseEnd_5493791 := by
    simpa [prefixWord, tailWord_5493791, baseEnd_5493791] using wordTrace_append hprefix tailTrace_5493791
  have hstable : (prefixWord ++ tailWord_5493791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493791).length < 2 ^ (prefixWord ++ tailWord_5493791).sum := by decide
  have hdescent : baseEnd_5493791 < baseStart_5493791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493822 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_5493822 : Nat := 118140960795 + 5493822 * 2 ^ 59
def prefixEnd_5493822 : Nat := 4983230072969 + 3 ^ 40 * 5493822 * 2
def baseEnd_5493822 : Nat := 2820971316245109629859379

theorem tailTrace_5493822 : CollatzResearch.WordTrace tailWord_5493822 prefixEnd_5493822 2820971316245109629859379 := by
  unfold tailWord_5493822
  simp only [CollatzResearch.WordTrace]
  refine ⟨25047018737853579867901465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133584099935219092628807813 25047018737853579867901465)
  ·
    refine ⟨18785264053390184900926099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25047018737853579867901465 18785264053390184900926099)
    ·
      refine ⟨28177896080085277351389149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18785264053390184900926099 28177896080085277351389149)
      ·
        refine ⟨10566711030031979006770931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28177896080085277351389149 10566711030031979006770931)
        ·
          refine ⟨15850066545047968510156397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10566711030031979006770931 15850066545047968510156397)
          ·
            refine ⟨5943774954392988191308649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15850066545047968510156397 5943774954392988191308649)
            ·
              refine ⟨4457831215794741143481487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943774954392988191308649 4457831215794741143481487)
              ·
                refine ⟨6686746823692111715222231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457831215794741143481487 6686746823692111715222231)
                ·
                  refine ⟨10030120235538167572833347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686746823692111715222231 10030120235538167572833347)
                  ·
                    refine ⟨15045180353307251359250021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10030120235538167572833347 15045180353307251359250021)
                    ·
                      refine ⟨2820971316245109629859379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15045180353307251359250021 2820971316245109629859379)
                      ·
                        rfl

theorem cell23_5493822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_5493822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493822 prefixEnd_5493822 := by exact prefixLift 5493822
  have htrace : WordTrace (prefixWord ++ tailWord_5493822) baseStart_5493822 baseEnd_5493822 := by
    simpa [prefixWord, tailWord_5493822, baseEnd_5493822] using wordTrace_append hprefix tailTrace_5493822
  have hstable : (prefixWord ++ tailWord_5493822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493822).length < 2 ^ (prefixWord ++ tailWord_5493822).sum := by decide
  have hdescent : baseEnd_5493822 < baseStart_5493822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493825 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_5493825 : Nat := 118140960795 + 5493825 * 2 ^ 59
def prefixEnd_5493825 : Nat := 4983230072969 + 3 ^ 40 * 5493825 * 2
def baseEnd_5493825 : Nat := 2820972856687073118121865

theorem tailTrace_5493825 : CollatzResearch.WordTrace tailWord_5493825 prefixEnd_5493825 2820972856687073118121865 := by
  unfold tailWord_5493825
  simp only [CollatzResearch.WordTrace]
  refine ⟨200376259321817770455570929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133584172881211846970380619 200376259321817770455570929)
  ·
    refine ⟨150282194491363327841678197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200376259321817770455570929 150282194491363327841678197)
    ·
      refine ⟨14088955733565311985157331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150282194491363327841678197 14088955733565311985157331)
      ·
        refine ⟨21133433600347967977735997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14088955733565311985157331 21133433600347967977735997)
        ·
          refine ⟨7925037600130487991650999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21133433600347967977735997 7925037600130487991650999)
          ·
            refine ⟨11887556400195731987476499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925037600130487991650999 11887556400195731987476499)
            ·
              refine ⟨17831334600293597981214749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11887556400195731987476499 17831334600293597981214749)
              ·
                refine ⟨6686750475110099242955531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17831334600293597981214749 6686750475110099242955531)
                ·
                  refine ⟨10030125712665148864433297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686750475110099242955531 10030125712665148864433297)
                  ·
                    refine ⟨7522594284498861648324973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10030125712665148864433297 7522594284498861648324973)
                    ·
                      refine ⟨2820972856687073118121865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7522594284498861648324973 2820972856687073118121865)
                      ·
                        rfl

theorem cell23_5493825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_5493825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493825 prefixEnd_5493825 := by exact prefixLift 5493825
  have htrace : WordTrace (prefixWord ++ tailWord_5493825) baseStart_5493825 baseEnd_5493825 := by
    simpa [prefixWord, tailWord_5493825, baseEnd_5493825] using wordTrace_append hprefix tailTrace_5493825
  have hstable : (prefixWord ++ tailWord_5493825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493825).length < 2 ^ (prefixWord ++ tailWord_5493825).sum := by decide
  have hdescent : baseEnd_5493825 < baseStart_5493825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493838 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_5493838 : Nat := 118140960795 + 5493838 * 2 ^ 59
def prefixEnd_5493838 : Nat := 4983230072969 + 3 ^ 40 * 5493838 * 2
def baseEnd_5493838 : Nat := 2820979531935581567259305

theorem tailTrace_5493838 : CollatzResearch.WordTrace tailWord_5493838 prefixEnd_5493838 2820979531935581567259305 := by
  unfold tailWord_5493838
  simp only [CollatzResearch.WordTrace]
  refine ⟨25047091683846334209474271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133584488980513782450529445 25047091683846334209474271)
  ·
    refine ⟨37570637525769501314211407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25047091683846334209474271 37570637525769501314211407)
    ·
      refine ⟨56355956288654251971317111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37570637525769501314211407 56355956288654251971317111)
      ·
        refine ⟨84533934432981377956975667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56355956288654251971317111 84533934432981377956975667)
        ·
          refine ⟨126800901649472066935463501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84533934432981377956975667 126800901649472066935463501)
          ·
            refine ⟨47550338118552025100798813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126800901649472066935463501 47550338118552025100798813)
            ·
              refine ⟨17831376794457009412799555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47550338118552025100798813 17831376794457009412799555)
              ·
                refine ⟨26747065191685514119199333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17831376794457009412799555 26747065191685514119199333)
                ·
                  refine ⟨5015074723441033897349875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26747065191685514119199333 5015074723441033897349875)
                  ·
                    refine ⟨7522612085161550846024813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5015074723441033897349875 7522612085161550846024813)
                    ·
                      refine ⟨2820979531935581567259305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7522612085161550846024813 2820979531935581567259305)
                      ·
                        rfl

theorem cell23_5493838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_5493838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493838 prefixEnd_5493838 := by exact prefixLift 5493838
  have htrace : WordTrace (prefixWord ++ tailWord_5493838) baseStart_5493838 baseEnd_5493838 := by
    simpa [prefixWord, tailWord_5493838, baseEnd_5493838] using wordTrace_append hprefix tailTrace_5493838
  have hstable : (prefixWord ++ tailWord_5493838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493838).length < 2 ^ (prefixWord ++ tailWord_5493838).sum := by decide
  have hdescent : baseEnd_5493838 < baseStart_5493838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493855 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 2, 1, 3]
def baseStart_5493855 : Nat := 118140960795 + 5493855 * 2 ^ 59
def prefixEnd_5493855 : Nat := 4983230072969 + 3 ^ 40 * 5493855 * 2
def baseEnd_5493855 : Nat := 2820988261106708000746727

theorem tailTrace_5493855 : CollatzResearch.WordTrace tailWord_5493855 prefixEnd_5493855 2820988261106708000746727 := by
  unfold tailWord_5493855
  simp only [CollatzResearch.WordTrace]
  refine ⟨200377353511709085579163019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133584902341139390386108679 200377353511709085579163019)
  ·
    refine ⟨300566030267563628368744529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200377353511709085579163019 300566030267563628368744529)
    ·
      refine ⟨225424522700672721276558397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300566030267563628368744529 225424522700672721276558397)
      ·
        refine ⟨84534196012752270478709399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225424522700672721276558397 84534196012752270478709399)
        ·
          refine ⟨126801294019128405718064099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84534196012752270478709399 126801294019128405718064099)
          ·
            refine ⟨190201941028692608577096149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126801294019128405718064099 190201941028692608577096149)
            ·
              refine ⟨4457857992859983013525691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 190201941028692608577096149 4457857992859983013525691)
              ·
                refine ⟨6686786989289974520288537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457857992859983013525691 6686786989289974520288537)
                ·
                  refine ⟨5015090241967480890216403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686786989289974520288537 5015090241967480890216403)
                  ·
                    refine ⟨7522635362951221335324605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5015090241967480890216403 7522635362951221335324605)
                    ·
                      refine ⟨2820988261106708000746727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7522635362951221335324605 2820988261106708000746727)
                      ·
                        rfl

theorem cell23_5493855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_5493855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493855 prefixEnd_5493855 := by exact prefixLift 5493855
  have htrace : WordTrace (prefixWord ++ tailWord_5493855) baseStart_5493855 baseEnd_5493855 := by
    simpa [prefixWord, tailWord_5493855, baseEnd_5493855] using wordTrace_append hprefix tailTrace_5493855
  have hstable : (prefixWord ++ tailWord_5493855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493855).length < 2 ^ (prefixWord ++ tailWord_5493855).sum := by decide
  have hdescent : baseEnd_5493855 < baseStart_5493855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493865 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 1, 3, 2]
def baseStart_5493865 : Nat := 118140960795 + 5493865 * 2 ^ 59
def prefixEnd_5493865 : Nat := 4983230072969 + 3 ^ 40 * 5493865 * 2
def baseEnd_5493865 : Nat := 2820993395913252961621681

theorem tailTrace_5493865 : CollatzResearch.WordTrace tailWord_5493865 prefixEnd_5493865 2820993395913252961621681 := by
  unfold tailWord_5493865
  simp only [CollatzResearch.WordTrace]
  refine ⟨200377718241672857287027049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133585145494448571524684699 200377718241672857287027049)
  ·
    refine ⟨150283288681254642965270287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200377718241672857287027049 150283288681254642965270287)
    ·
      refine ⟨225424933021881964447905431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150283288681254642965270287 225424933021881964447905431)
      ·
        refine ⟨338137399532822946671858147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225424933021881964447905431 338137399532822946671858147)
        ·
          refine ⟨507206099299234420007787221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338137399532822946671858147 507206099299234420007787221)
          ·
            refine ⟨11887642952325806718932513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 507206099299234420007787221 11887642952325806718932513)
            ·
              refine ⟨8915732214244355039199385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11887642952325806718932513 8915732214244355039199385)
              ·
                refine ⟨6686799160683266279399539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8915732214244355039199385 6686799160683266279399539)
                ·
                  refine ⟨10030198741024899419099309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6686799160683266279399539 10030198741024899419099309)
                  ·
                    refine ⟨3761324527884337282162241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10030198741024899419099309 3761324527884337282162241)
                    ·
                      refine ⟨2820993395913252961621681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761324527884337282162241 2820993395913252961621681)
                      ·
                        rfl

theorem cell23_5493865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 3, 2].length) (baseStart_5493865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493865 prefixEnd_5493865 := by exact prefixLift 5493865
  have htrace : WordTrace (prefixWord ++ tailWord_5493865) baseStart_5493865 baseEnd_5493865 := by
    simpa [prefixWord, tailWord_5493865, baseEnd_5493865] using wordTrace_append hprefix tailTrace_5493865
  have hstable : (prefixWord ++ tailWord_5493865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493865).length < 2 ^ (prefixWord ++ tailWord_5493865).sum := by decide
  have hdescent : baseEnd_5493865 < baseStart_5493865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493895 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_5493895 : Nat := 118140960795 + 5493895 * 2 ^ 59
def prefixEnd_5493895 : Nat := 4983230072969 + 3 ^ 40 * 5493895 * 2
def baseEnd_5493895 : Nat := 2821008800332887844246543

theorem tailTrace_5493895 : CollatzResearch.WordTrace tailWord_5493895 prefixEnd_5493895 2821008800332887844246543 := by
  unfold tailWord_5493895
  simp only [CollatzResearch.WordTrace]
  refine ⟨200378812431564172410619139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133585874954376114940412759 200378812431564172410619139)
  ·
    refine ⟨300568218647346258615928709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200378812431564172410619139 300568218647346258615928709)
    ·
      refine ⟨56356540996377423490486633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300568218647346258615928709 56356540996377423490486633)
      ·
        refine ⟨42267405747283067617864975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56356540996377423490486633 42267405747283067617864975)
        ·
          refine ⟨63401108620924601426797463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42267405747283067617864975 63401108620924601426797463)
          ·
            refine ⟨95101662931386902140196195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63401108620924601426797463 95101662931386902140196195)
            ·
              refine ⟨142652494397080353210294293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95101662931386902140196195 142652494397080353210294293)
              ·
                refine ⟨6686835674863141556732545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142652494397080353210294293 6686835674863141556732545)
                ·
                  refine ⟨5015126756147356167549409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686835674863141556732545 5015126756147356167549409)
                  ·
                    refine ⟨3761345067110517125662057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5015126756147356167549409 3761345067110517125662057)
                    ·
                      refine ⟨2821008800332887844246543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761345067110517125662057 2821008800332887844246543)
                      ·
                        rfl

theorem cell23_5493895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_5493895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493895 prefixEnd_5493895 := by exact prefixLift 5493895
  have htrace : WordTrace (prefixWord ++ tailWord_5493895) baseStart_5493895 baseEnd_5493895 := by
    simpa [prefixWord, tailWord_5493895, baseEnd_5493895] using wordTrace_append hprefix tailTrace_5493895
  have hstable : (prefixWord ++ tailWord_5493895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493895).length < 2 ^ (prefixWord ++ tailWord_5493895).sum := by decide
  have hdescent : baseEnd_5493895 < baseStart_5493895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493904 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_5493904 : Nat := 118140960795 + 5493904 * 2 ^ 59
def prefixEnd_5493904 : Nat := 4983230072969 + 3 ^ 40 * 5493904 * 2
def baseEnd_5493904 : Nat := 2821013421658778309034001

theorem tailTrace_5493904 : CollatzResearch.WordTrace tailWord_5493904 prefixEnd_5493904 2821013421658778309034001 := by
  unfold tailWord_5493904
  simp only [CollatzResearch.WordTrace]
  refine ⟨100189570344265783473848383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133586093792354377965131177 100189570344265783473848383)
  ·
    refine ⟨150284355516398675210772575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100189570344265783473848383 150284355516398675210772575)
    ·
      refine ⟨225426533274598012816158863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150284355516398675210772575 225426533274598012816158863)
      ·
        refine ⟨338139799911897019224238295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225426533274598012816158863 338139799911897019224238295)
        ·
          refine ⟨507209699867845528836357443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338139799911897019224238295 507209699867845528836357443)
          ·
            refine ⟨760814549801768293254536165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507209699867845528836357443 760814549801768293254536165)
            ·
              refine ⟨142652728087831554985225531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 760814549801768293254536165 142652728087831554985225531)
              ·
                refine ⟨213979092131747332477838297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142652728087831554985225531 213979092131747332477838297)
                ·
                  refine ⟨160484319098810499358378723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213979092131747332477838297 160484319098810499358378723)
                  ·
                    refine ⟨240726478648215749037568085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160484319098810499358378723 240726478648215749037568085)
                    ·
                      refine ⟨2821013421658778309034001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 240726478648215749037568085 2821013421658778309034001)
                      ·
                        rfl

theorem cell23_5493904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_5493904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493904 prefixEnd_5493904 := by exact prefixLift 5493904
  have htrace : WordTrace (prefixWord ++ tailWord_5493904) baseStart_5493904 baseEnd_5493904 := by
    simpa [prefixWord, tailWord_5493904, baseEnd_5493904] using wordTrace_append hprefix tailTrace_5493904
  have hstable : (prefixWord ++ tailWord_5493904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493904).length < 2 ^ (prefixWord ++ tailWord_5493904).sum := by decide
  have hdescent : baseEnd_5493904 < baseStart_5493904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493912 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5493912 : Nat := 118140960795 + 5493912 * 2 ^ 59
def prefixEnd_5493912 : Nat := 4983230072969 + 3 ^ 40 * 5493912 * 2
def baseEnd_5493912 : Nat := 2821017529504014277733965

theorem tailTrace_5493912 : CollatzResearch.WordTrace tailWord_5493912 prefixEnd_5493912 2821017529504014277733965 := by
  unfold tailWord_5493912
  simp only [CollatzResearch.WordTrace]
  refine ⟨100189716236251292156993995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133586288315001722875991993 100189716236251292156993995)
  ·
    refine ⟨150284574354376938235490993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100189716236251292156993995 150284574354376938235490993)
    ·
      refine ⟨112713430765782703676618245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150284574354376938235490993 112713430765782703676618245)
      ·
        refine ⟨21133768268584256939365921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112713430765782703676618245 21133768268584256939365921)
        ·
          refine ⟨15850326201438192704524441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21133768268584256939365921 15850326201438192704524441)
          ·
            refine ⟨11887744651078644528393331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15850326201438192704524441 11887744651078644528393331)
            ·
              refine ⟨17831616976617966792589997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11887744651078644528393331 17831616976617966792589997)
              ·
                refine ⟨6686856366231737547221249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17831616976617966792589997 6686856366231737547221249)
                ·
                  refine ⟨5015142274673803160415937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686856366231737547221249 5015142274673803160415937)
                  ·
                    refine ⟨3761356706005352370311953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5015142274673803160415937 3761356706005352370311953)
                    ·
                      refine ⟨2821017529504014277733965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761356706005352370311953 2821017529504014277733965)
                      ·
                        rfl

theorem cell23_5493912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5493912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493912 prefixEnd_5493912 := by exact prefixLift 5493912
  have htrace : WordTrace (prefixWord ++ tailWord_5493912) baseStart_5493912 baseEnd_5493912 := by
    simpa [prefixWord, tailWord_5493912, baseEnd_5493912] using wordTrace_append hprefix tailTrace_5493912
  have hstable : (prefixWord ++ tailWord_5493912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493912).length < 2 ^ (prefixWord ++ tailWord_5493912).sum := by decide
  have hdescent : baseEnd_5493912 < baseStart_5493912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493948 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_5493948 : Nat := 118140960795 + 5493948 * 2 ^ 59
def prefixEnd_5493948 : Nat := 4983230072969 + 3 ^ 40 * 5493948 * 2
def baseEnd_5493948 : Nat := 940345338269192045627933

theorem tailTrace_5493948 : CollatzResearch.WordTrace tailWord_5493948 prefixEnd_5493948 940345338269192045627933 := by
  unfold tailWord_5493948
  simp only [CollatzResearch.WordTrace]
  refine ⟨100190372750186081231149249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133587163666914774974865665 100190372750186081231149249)
  ·
    refine ⟨75142779562639560923361937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100190372750186081231149249 75142779562639560923361937)
    ·
      refine ⟨56357084671979670692521453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75142779562639560923361937 56357084671979670692521453)
      ·
        refine ⟨21133906751992376509695545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56357084671979670692521453 21133906751992376509695545)
        ·
          refine ⟨15850430063994282382271659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21133906751992376509695545 15850430063994282382271659)
          ·
            refine ⟨23775645095991423573407489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15850430063994282382271659 23775645095991423573407489)
            ·
              refine ⟨17831733821993567680055617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23775645095991423573407489 17831733821993567680055617)
              ·
                refine ⟨13373800366495175760041713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17831733821993567680055617 13373800366495175760041713)
                ·
                  refine ⟨10030350274871381820031285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13373800366495175760041713 10030350274871381820031285)
                  ·
                    refine ⟨940345338269192045627933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10030350274871381820031285 940345338269192045627933)
                    ·
                      rfl

theorem cell23_5493948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_5493948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493948 prefixEnd_5493948 := by exact prefixLift 5493948
  have htrace : WordTrace (prefixWord ++ tailWord_5493948) baseStart_5493948 baseEnd_5493948 := by
    simpa [prefixWord, tailWord_5493948, baseEnd_5493948] using wordTrace_append hprefix tailTrace_5493948
  have hstable : (prefixWord ++ tailWord_5493948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493948).length < 2 ^ (prefixWord ++ tailWord_5493948).sum := by decide
  have hdescent : baseEnd_5493948 < baseStart_5493948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493952 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 5]
def baseStart_5493952 : Nat := 118140960795 + 5493952 * 2 ^ 59
def prefixEnd_5493952 : Nat := 4983230072969 + 3 ^ 40 * 5493952 * 2
def baseEnd_5493952 : Nat := 313448674303354902359309

theorem tailTrace_5493952 : CollatzResearch.WordTrace tailWord_5493952 prefixEnd_5493952 313448674303354902359309 := by
  unfold tailWord_5493952
  simp only [CollatzResearch.WordTrace]
  refine ⟨100190445696178835572722055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133587260928238447430296073 100190445696178835572722055)
  ·
    refine ⟨150285668544268253359083083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100190445696178835572722055 150285668544268253359083083)
    ·
      refine ⟨225428502816402380038624625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150285668544268253359083083 225428502816402380038624625)
      ·
        refine ⟨169071377112301785028968469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225428502816402380038624625 169071377112301785028968469)
        ·
          refine ⟨7925220802139146173232897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169071377112301785028968469 7925220802139146173232897)
          ·
            refine ⟨5943915601604359629924673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925220802139146173232897 5943915601604359629924673)
            ·
              refine ⟨4457936701203269722443505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943915601604359629924673 4457936701203269722443505)
              ·
                refine ⟨3343452525902452291832629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4457936701203269722443505 3343452525902452291832629)
                ·
                  refine ⟨313448674303354902359309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3343452525902452291832629 313448674303354902359309)
                  ·
                    rfl

theorem cell23_5493952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 5].length) (baseStart_5493952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493952 prefixEnd_5493952 := by exact prefixLift 5493952
  have htrace : WordTrace (prefixWord ++ tailWord_5493952) baseStart_5493952 baseEnd_5493952 := by
    simpa [prefixWord, tailWord_5493952, baseEnd_5493952] using wordTrace_append hprefix tailTrace_5493952
  have hstable : (prefixWord ++ tailWord_5493952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493952).length < 2 ^ (prefixWord ++ tailWord_5493952).sum := by decide
  have hdescent : baseEnd_5493952 < baseStart_5493952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493971 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 3]
def baseStart_5493971 : Nat := 118140960795 + 5493971 * 2 ^ 59
def prefixEnd_5493971 : Nat := 4983230072969 + 3 ^ 40 * 5493971 * 2
def baseEnd_5493971 : Nat := 2821047824862629546896193

theorem tailTrace_5493971 : CollatzResearch.WordTrace tailWord_5493971 prefixEnd_5493971 2821047824862629546896193 := by
  unfold tailWord_5493971
  simp only [CollatzResearch.WordTrace]
  refine ⟨200381584379288837390385767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133587722919525891593590511 200381584379288837390385767)
  ·
    refine ⟨300572376568933256085578651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200381584379288837390385767 300572376568933256085578651)
    ·
      refine ⟨450858564853399884128367977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300572376568933256085578651 450858564853399884128367977)
      ·
        refine ⟨338143923640049913096275983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450858564853399884128367977 338143923640049913096275983)
        ·
          refine ⟨507215885460074869644413975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338143923640049913096275983 507215885460074869644413975)
          ·
            refine ⟨760823828190112304466620963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507215885460074869644413975 760823828190112304466620963)
            ·
              refine ⟨1141235742285168456699931445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760823828190112304466620963 1141235742285168456699931445)
              ·
                refine ⟨106990850839234542815618573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1141235742285168456699931445 106990850839234542815618573)
                ·
                  refine ⟨40121569064712953555856965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106990850839234542815618573 40121569064712953555856965)
                  ·
                    refine ⟨7522794199633678791723181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40121569064712953555856965 7522794199633678791723181)
                    ·
                      refine ⟨2821047824862629546896193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7522794199633678791723181 2821047824862629546896193)
                      ·
                        rfl

theorem cell23_5493971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_5493971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493971 prefixEnd_5493971 := by exact prefixLift 5493971
  have htrace : WordTrace (prefixWord ++ tailWord_5493971) baseStart_5493971 baseEnd_5493971 := by
    simpa [prefixWord, tailWord_5493971, baseEnd_5493971] using wordTrace_append hprefix tailTrace_5493971
  have hstable : (prefixWord ++ tailWord_5493971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493971).length < 2 ^ (prefixWord ++ tailWord_5493971).sum := by decide
  have hdescent : baseEnd_5493971 < baseStart_5493971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493985 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_5493985 : Nat := 118140960795 + 5493985 * 2 ^ 59
def prefixEnd_5493985 : Nat := 4983230072969 + 3 ^ 40 * 5493985 * 2
def baseEnd_5493985 : Nat := 2821055013591792492121129

theorem tailTrace_5493985 : CollatzResearch.WordTrace tailWord_5493985 prefixEnd_5493985 2821055013591792492121129 := by
  unfold tailWord_5493985
  simp only [CollatzResearch.WordTrace]
  refine ⟨200382095001238117781395409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133588063334158745187596939 200382095001238117781395409)
  ·
    refine ⟨150286571250928588336046557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200382095001238117781395409 150286571250928588336046557)
    ·
      refine ⟨56357464219098220626017459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150286571250928588336046557 56357464219098220626017459)
      ·
        refine ⟨84536196328647330939026189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56357464219098220626017459 84536196328647330939026189)
        ·
          refine ⟨31701073623242749102134821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84536196328647330939026189 31701073623242749102134821)
          ·
            refine ⟨5943951304358015456650279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31701073623242749102134821 5943951304358015456650279)
            ·
              refine ⟨8915926956537023184975419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943951304358015456650279 8915926956537023184975419)
              ·
                refine ⟨13373890434805534777463129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8915926956537023184975419 13373890434805534777463129)
                ·
                  refine ⟨10030417826104151083097347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13373890434805534777463129 10030417826104151083097347)
                  ·
                    refine ⟨15045626739156226624646021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10030417826104151083097347 15045626739156226624646021)
                    ·
                      refine ⟨2821055013591792492121129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15045626739156226624646021 2821055013591792492121129)
                      ·
                        rfl

theorem cell23_5493985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_5493985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493985 prefixEnd_5493985 := by exact prefixLift 5493985
  have htrace : WordTrace (prefixWord ++ tailWord_5493985) baseStart_5493985 baseEnd_5493985 := by
    simpa [prefixWord, tailWord_5493985, baseEnd_5493985] using wordTrace_append hprefix tailTrace_5493985
  have hstable : (prefixWord ++ tailWord_5493985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493985).length < 2 ^ (prefixWord ++ tailWord_5493985).sum := by decide
  have hdescent : baseEnd_5493985 < baseStart_5493985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5493995 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 1, 4]
def baseStart_5493995 : Nat := 118140960795 + 5493995 * 2 ^ 59
def prefixEnd_5493995 : Nat := 4983230072969 + 3 ^ 40 * 5493995 * 2
def baseEnd_5493995 : Nat := 940353382799445817665361

theorem tailTrace_5493995 : CollatzResearch.WordTrace tailWord_5493995 prefixEnd_5493995 940353382799445817665361 := by
  unfold tailWord_5493995
  simp only [CollatzResearch.WordTrace]
  refine ⟨200382459731201889489259439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133588306487467926326172959 200382459731201889489259439)
  ·
    refine ⟨300573689596802834233889159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200382459731201889489259439 300573689596802834233889159)
    ·
      refine ⟨450860534395204251350833739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300573689596802834233889159 450860534395204251350833739)
      ·
        refine ⟨676290801592806377026250609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450860534395204251350833739 676290801592806377026250609)
        ·
          refine ⟨507218101194604782769687957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676290801592806377026250609 507218101194604782769687957)
          ·
            refine ⟨23775848493497099192329123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 507218101194604782769687957 23775848493497099192329123)
            ·
              refine ⟨35663772740245648788493685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23775848493497099192329123 35663772740245648788493685)
              ·
                refine ⟨3343478694398029573921283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35663772740245648788493685 3343478694398029573921283)
                ·
                  refine ⟨5015218041597044360881925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343478694398029573921283 5015218041597044360881925)
                  ·
                    refine ⟨940353382799445817665361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015218041597044360881925 940353382799445817665361)
                    ·
                      rfl

theorem cell23_5493995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 4].length) (baseStart_5493995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5493995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5493995 prefixEnd_5493995 := by exact prefixLift 5493995
  have htrace : WordTrace (prefixWord ++ tailWord_5493995) baseStart_5493995 baseEnd_5493995 := by
    simpa [prefixWord, tailWord_5493995, baseEnd_5493995] using wordTrace_append hprefix tailTrace_5493995
  have hstable : (prefixWord ++ tailWord_5493995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5493995).length < 2 ^ (prefixWord ++ tailWord_5493995).sum := by decide
  have hdescent : baseEnd_5493995 < baseStart_5493995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5493995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494041 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_5494041 : Nat := 118140960795 + 5494041 * 2 ^ 59
def prefixEnd_5494041 : Nat := 4983230072969 + 3 ^ 40 * 5494041 * 2
def baseEnd_5494041 : Nat := 2821083768508444273020871

theorem tailTrace_5494041 : CollatzResearch.WordTrace tailWord_5494041 prefixEnd_5494041 2821083768508444273020871 := by
  unfold tailWord_5494041
  simp only [CollatzResearch.WordTrace]
  refine ⟨200384137489035239345433977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133589424992690159563622651 200384137489035239345433977)
  ·
    refine ⟨150288103116776429509075483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200384137489035239345433977 150288103116776429509075483)
    ·
      refine ⟨225432154675164644263613225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150288103116776429509075483 225432154675164644263613225)
      ·
        refine ⟨169074116006373483197709919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225432154675164644263613225 169074116006373483197709919)
        ·
          refine ⟨253611174009560224796564879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169074116006373483197709919 253611174009560224796564879)
          ·
            refine ⟨380416761014340337194847319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253611174009560224796564879 380416761014340337194847319)
            ·
              refine ⟨570625141521510505792270979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380416761014340337194847319 570625141521510505792270979)
              ·
                refine ⟨855937712282265758688406469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570625141521510505792270979 855937712282265758688406469)
                ·
                  refine ⟨160488321052924829754076213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855937712282265758688406469 160488321052924829754076213)
                  ·
                    refine ⟨15045780098711702789444645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160488321052924829754076213 15045780098711702789444645)
                    ·
                      refine ⟨2821083768508444273020871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15045780098711702789444645 2821083768508444273020871)
                      ·
                        rfl

theorem cell23_5494041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_5494041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494041 prefixEnd_5494041 := by exact prefixLift 5494041
  have htrace : WordTrace (prefixWord ++ tailWord_5494041) baseStart_5494041 baseEnd_5494041 := by
    simpa [prefixWord, tailWord_5494041, baseEnd_5494041] using wordTrace_append hprefix tailTrace_5494041
  have hstable : (prefixWord ++ tailWord_5494041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494041).length < 2 ^ (prefixWord ++ tailWord_5494041).sum := by decide
  have hdescent : baseEnd_5494041 < baseStart_5494041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494088 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_5494088 : Nat := 118140960795 + 5494088 * 2 ^ 59
def prefixEnd_5494088 : Nat := 4983230072969 + 3 ^ 40 * 5494088 * 2
def baseEnd_5494088 : Nat := 2821107902099205589133155

theorem tailTrace_5494088 : CollatzResearch.WordTrace tailWord_5494088 prefixEnd_5494088 2821107902099205589133155 := by
  unfold tailWord_5494088
  simp only [CollatzResearch.WordTrace]
  refine ⟨100192925859932483186197459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133590567813243310914929945 100192925859932483186197459)
  ·
    refine ⟨150289388789898724779296189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100192925859932483186197459 150289388789898724779296189)
    ·
      refine ⟨56358520796212021792236071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150289388789898724779296189 56358520796212021792236071)
      ·
        refine ⟨84537781194318032688354107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56358520796212021792236071 84537781194318032688354107)
        ·
          refine ⟨126806671791477049032531161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84537781194318032688354107 126806671791477049032531161)
          ·
            refine ⟨95105003843607786774398371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126806671791477049032531161 95105003843607786774398371)
            ·
              refine ⟨142657505765411680161597557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95105003843607786774398371 142657505765411680161597557)
              ·
                refine ⟨13374141165507345015149771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142657505765411680161597557 13374141165507345015149771)
                ·
                  refine ⟨20061211748261017522724657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13374141165507345015149771 20061211748261017522724657)
                  ·
                    refine ⟨15045908811195763142043493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20061211748261017522724657 15045908811195763142043493)
                    ·
                      refine ⟨2821107902099205589133155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15045908811195763142043493 2821107902099205589133155)
                      ·
                        rfl

theorem cell23_5494088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_5494088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494088 prefixEnd_5494088 := by exact prefixLift 5494088
  have htrace : WordTrace (prefixWord ++ tailWord_5494088) baseStart_5494088 baseEnd_5494088 := by
    simpa [prefixWord, tailWord_5494088, baseEnd_5494088] using wordTrace_append hprefix tailTrace_5494088
  have hstable : (prefixWord ++ tailWord_5494088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494088).length < 2 ^ (prefixWord ++ tailWord_5494088).sum := by decide
  have hdescent : baseEnd_5494088 < baseStart_5494088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494092 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_5494092 : Nat := 118140960795 + 5494092 * 2 ^ 59
def prefixEnd_5494092 : Nat := 4983230072969 + 3 ^ 40 * 5494092 * 2
def baseEnd_5494092 : Nat := 2821109956021823573483137

theorem tailTrace_5494092 : CollatzResearch.WordTrace tailWord_5494092 prefixEnd_5494092 2821109956021823573483137 := by
  unfold tailWord_5494092
  simp only [CollatzResearch.WordTrace]
  refine ⟨100192998805925237527770265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133590665074566983370360353 100192998805925237527770265)
  ·
    refine ⟨75144749104443928145827699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100192998805925237527770265 75144749104443928145827699)
    ·
      refine ⟨112717123656665892218741549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75144749104443928145827699 112717123656665892218741549)
      ·
        refine ⟨42268921371249709582028081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112717123656665892218741549 42268921371249709582028081)
        ·
          refine ⟨31701691028437282186521061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42268921371249709582028081 31701691028437282186521061)
          ·
            refine ⟨5944067067831990409972699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31701691028437282186521061 5944067067831990409972699)
            ·
              refine ⟨8916100601747985614959049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944067067831990409972699 8916100601747985614959049)
              ·
                refine ⟨6687075451310989211219287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8916100601747985614959049 6687075451310989211219287)
                ·
                  refine ⟨10030613176966483816828931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687075451310989211219287 10030613176966483816828931)
                  ·
                    refine ⟨15045919765449725725243397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10030613176966483816828931 15045919765449725725243397)
                    ·
                      refine ⟨2821109956021823573483137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15045919765449725725243397 2821109956021823573483137)
                      ·
                        rfl

theorem cell23_5494092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_5494092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494092 prefixEnd_5494092 := by exact prefixLift 5494092
  have htrace : WordTrace (prefixWord ++ tailWord_5494092) baseStart_5494092 baseEnd_5494092 := by
    simpa [prefixWord, tailWord_5494092, baseEnd_5494092] using wordTrace_append hprefix tailTrace_5494092
  have hstable : (prefixWord ++ tailWord_5494092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494092).length < 2 ^ (prefixWord ++ tailWord_5494092).sum := by decide
  have hdescent : baseEnd_5494092 < baseStart_5494092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494135 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 5, 3, 2]
def baseStart_5494135 : Nat := 118140960795 + 5494135 * 2 ^ 59
def prefixEnd_5494135 : Nat := 4983230072969 + 3 ^ 40 * 5494135 * 2
def baseEnd_5494135 : Nat := 2821132035689966905245439

theorem tailTrace_5494135 : CollatzResearch.WordTrace tailWord_5494135 prefixEnd_5494135 2821132035689966905245439 := by
  unfold tailWord_5494135
  simp only [CollatzResearch.WordTrace]
  refine ⟨200387565950694693399355859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133591710633796462266237239 200387565950694693399355859)
  ·
    refine ⟨300581348926042040099033789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200387565950694693399355859 300581348926042040099033789)
    ·
      refine ⟨112718005847265765037137671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300581348926042040099033789 112718005847265765037137671)
      ·
        refine ⟨169077008770898647555706507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112718005847265765037137671 169077008770898647555706507)
        ·
          refine ⟨253615513156347971333559761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169077008770898647555706507 253615513156347971333559761)
          ·
            refine ⟨190211634867260978500169821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253615513156347971333559761 190211634867260978500169821)
            ·
              refine ⟨71329363075222866937563683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190211634867260978500169821 71329363075222866937563683)
              ·
                refine ⟨106994044612834300406345525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71329363075222866937563683 106994044612834300406345525)
                ·
                  refine ⟨10030691682453215663094893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106994044612834300406345525 10030691682453215663094893)
                  ·
                    refine ⟨3761509380919955873660585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10030691682453215663094893 3761509380919955873660585)
                    ·
                      refine ⟨2821132035689966905245439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761509380919955873660585 2821132035689966905245439)
                      ·
                        rfl

theorem cell23_5494135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_5494135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494135 prefixEnd_5494135 := by exact prefixLift 5494135
  have htrace : WordTrace (prefixWord ++ tailWord_5494135) baseStart_5494135 baseEnd_5494135 := by
    simpa [prefixWord, tailWord_5494135, baseEnd_5494135] using wordTrace_append hprefix tailTrace_5494135
  have hstable : (prefixWord ++ tailWord_5494135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494135).length < 2 ^ (prefixWord ++ tailWord_5494135).sum := by decide
  have hdescent : baseEnd_5494135 < baseStart_5494135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494152 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_5494152 : Nat := 118140960795 + 5494152 * 2 ^ 59
def prefixEnd_5494152 : Nat := 4983230072969 + 3 ^ 40 * 5494152 * 2
def baseEnd_5494152 : Nat := 2821140764861093338732861

theorem tailTrace_5494152 : CollatzResearch.WordTrace tailWord_5494152 prefixEnd_5494152 2821140764861093338732861 := by
  unfold tailWord_5494152
  simp only [CollatzResearch.WordTrace]
  refine ⟨100194092995816552651362355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133592123994422070201816473 100194092995816552651362355)
  ·
    refine ⟨150291139493724828977043533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100194092995816552651362355 150291139493724828977043533)
    ·
      refine ⟨56359177310146810866391325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150291139493724828977043533 56359177310146810866391325)
      ·
        refine ⟨21134691491305054074896747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56359177310146810866391325 21134691491305054074896747)
        ·
          refine ⟨31702037236957581112345121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21134691491305054074896747 31702037236957581112345121)
          ·
            refine ⟨23776527927718185834258841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31702037236957581112345121 23776527927718185834258841)
            ·
              refine ⟨17832395945788639375694131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23776527927718185834258841 17832395945788639375694131)
              ·
                refine ⟨26748593918682959063541197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17832395945788639375694131 26748593918682959063541197)
                ·
                  refine ⟨10030722719506109648827949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26748593918682959063541197 10030722719506109648827949)
                  ·
                    refine ⟨3761521019814791118310481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10030722719506109648827949 3761521019814791118310481)
                    ·
                      refine ⟨2821140764861093338732861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761521019814791118310481 2821140764861093338732861)
                      ·
                        rfl

theorem cell23_5494152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_5494152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494152 prefixEnd_5494152 := by exact prefixLift 5494152
  have htrace : WordTrace (prefixWord ++ tailWord_5494152) baseStart_5494152 baseEnd_5494152 := by
    simpa [prefixWord, tailWord_5494152, baseEnd_5494152] using wordTrace_append hprefix tailTrace_5494152
  have hstable : (prefixWord ++ tailWord_5494152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494152).length < 2 ^ (prefixWord ++ tailWord_5494152).sum := by decide
  have hdescent : baseEnd_5494152 < baseStart_5494152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494169 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 1, 3, 2]
def baseStart_5494169 : Nat := 118140960795 + 5494169 * 2 ^ 59
def prefixEnd_5494169 : Nat := 4983230072969 + 3 ^ 40 * 5494169 * 2
def baseEnd_5494169 : Nat := 2821149494032219772220283

theorem tailTrace_5494169 : CollatzResearch.WordTrace tailWord_5494169 prefixEnd_5494169 2821149494032219772220283 := by
  unfold tailWord_5494169
  simp only [CollatzResearch.WordTrace]
  refine ⟨200388806032571517206093561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133592537355047678137395707 200388806032571517206093561)
  ·
    refine ⟨150291604524428637904570171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200388806032571517206093561 150291604524428637904570171)
    ·
      refine ⟨225437406786642956856855257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150291604524428637904570171 225437406786642956856855257)
      ·
        refine ⟨169078055089982217642641443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225437406786642956856855257 169078055089982217642641443)
        ·
          refine ⟨253617082634973326463962165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169078055089982217642641443 253617082634973326463962165)
          ·
            refine ⟨23776601497028749355996453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 253617082634973326463962165 23776601497028749355996453)
            ·
              refine ⟨4458112780692890504249335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23776601497028749355996453 4458112780692890504249335)
              ·
                refine ⟨6687169171039335756374003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458112780692890504249335 6687169171039335756374003)
                ·
                  refine ⟨10030753756559003634561005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687169171039335756374003 10030753756559003634561005)
                  ·
                    refine ⟨3761532658709626362960377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10030753756559003634561005 3761532658709626362960377)
                    ·
                      refine ⟨2821149494032219772220283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761532658709626362960377 2821149494032219772220283)
                      ·
                        rfl

theorem cell23_5494169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_5494169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494169 prefixEnd_5494169 := by exact prefixLift 5494169
  have htrace : WordTrace (prefixWord ++ tailWord_5494169) baseStart_5494169 baseEnd_5494169 := by
    simpa [prefixWord, tailWord_5494169, baseEnd_5494169] using wordTrace_append hprefix tailTrace_5494169
  have hstable : (prefixWord ++ tailWord_5494169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494169).length < 2 ^ (prefixWord ++ tailWord_5494169).sum := by decide
  have hdescent : baseEnd_5494169 < baseStart_5494169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494188 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 7]
def baseStart_5494188 : Nat := 118140960795 + 5494188 * 2 ^ 59
def prefixEnd_5494188 : Nat := 4983230072969 + 3 ^ 40 * 5494188 * 2
def baseEnd_5494188 : Nat := 313462138907183910875855

theorem tailTrace_5494188 : CollatzResearch.WordTrace tailWord_5494188 prefixEnd_5494188 313462138907183910875855 := by
  unfold tailWord_5494188
  simp only [CollatzResearch.WordTrace]
  refine ⟨100194749509751341725517609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133592999346335122300690145 100194749509751341725517609)
  ·
    refine ⟨75146062132313506294138207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100194749509751341725517609 75146062132313506294138207)
    ·
      refine ⟨112719093198470259441207311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75146062132313506294138207 112719093198470259441207311)
      ·
        refine ⟨169078639797705389161810967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112719093198470259441207311 169078639797705389161810967)
        ·
          refine ⟨253617959696558083742716451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169078639797705389161810967 253617959696558083742716451)
          ·
            refine ⟨380426939544837125614074677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253617959696558083742716451 380426939544837125614074677)
            ·
              refine ⟨35665025582328480526319501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 380426939544837125614074677 35665025582328480526319501)
              ·
                refine ⟨13374384593373180197369813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35665025582328480526319501 13374384593373180197369813)
                ·
                  refine ⟨313462138907183910875855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13374384593373180197369813 313462138907183910875855)
                  ·
                    rfl

theorem cell23_5494188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_5494188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494188 prefixEnd_5494188 := by exact prefixLift 5494188
  have htrace : WordTrace (prefixWord ++ tailWord_5494188) baseStart_5494188 baseEnd_5494188 := by
    simpa [prefixWord, tailWord_5494188, baseEnd_5494188] using wordTrace_append hprefix tailTrace_5494188
  have hstable : (prefixWord ++ tailWord_5494188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494188).length < 2 ^ (prefixWord ++ tailWord_5494188).sum := by decide
  have hdescent : baseEnd_5494188 < baseStart_5494188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494222 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_5494222 : Nat := 118140960795 + 5494222 * 2 ^ 59
def prefixEnd_5494222 : Nat := 4983230072969 + 3 ^ 40 * 5494222 * 2
def baseEnd_5494222 : Nat := 313464078722989784984171

theorem tailTrace_5494222 : CollatzResearch.WordTrace tailWord_5494222 prefixEnd_5494222 313464078722989784984171 := by
  unfold tailWord_5494222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25048842387672438407221615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133593826067586338171848613 25048842387672438407221615)
  ·
    refine ⟨37573263581508657610832423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25048842387672438407221615 37573263581508657610832423)
    ·
      refine ⟨56359895372262986416248635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37573263581508657610832423 56359895372262986416248635)
      ·
        refine ⟨84539843058394479624372953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56359895372262986416248635 84539843058394479624372953)
        ·
          refine ⟨63404882293795859718279715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84539843058394479624372953 63404882293795859718279715)
          ·
            refine ⟨95107323440693789577419573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63404882293795859718279715 95107323440693789577419573)
            ·
              refine ⟨8916311572565042772883085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95107323440693789577419573 8916311572565042772883085)
              ·
                refine ⟨3343616839711891039831157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8916311572565042772883085 3343616839711891039831157)
                ·
                  refine ⟨313464078722989784984171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3343616839711891039831157 313464078722989784984171)
                  ·
                    rfl

theorem cell23_5494222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_5494222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494222 prefixEnd_5494222 := by exact prefixLift 5494222
  have htrace : WordTrace (prefixWord ++ tailWord_5494222) baseStart_5494222 baseEnd_5494222 := by
    simpa [prefixWord, tailWord_5494222, baseEnd_5494222] using wordTrace_append hprefix tailTrace_5494222
  have hstable : (prefixWord ++ tailWord_5494222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494222).length < 2 ^ (prefixWord ++ tailWord_5494222).sum := by decide
  have hdescent : baseEnd_5494222 < baseStart_5494222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494225 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 7, 2]
def baseStart_5494225 : Nat := 118140960795 + 5494225 * 2 ^ 59
def prefixEnd_5494225 : Nat := 4983230072969 + 3 ^ 40 * 5494225 * 2
def baseEnd_5494225 : Nat := 2821178248948871553120025

theorem tailTrace_5494225 : CollatzResearch.WordTrace tailWord_5494225 prefixEnd_5494225 2821178248948871553120025 := by
  unfold tailWord_5494225
  simp only [CollatzResearch.WordTrace]
  refine ⟨200390848520368638770132129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133593899013579092513421419 200390848520368638770132129)
  ·
    refine ⟨150293136390276479077599097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200390848520368638770132129 150293136390276479077599097)
    ·
      refine ⟨112719852292707359308199323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150293136390276479077599097 112719852292707359308199323)
      ·
        refine ⟨169079778439061038962298985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112719852292707359308199323 169079778439061038962298985)
        ·
          refine ⟨126809833829295779221724239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169079778439061038962298985 126809833829295779221724239)
          ·
            refine ⟨190214750743943668832586359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126809833829295779221724239 190214750743943668832586359)
            ·
              refine ⟨285322126115915503248879539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190214750743943668832586359 285322126115915503248879539)
              ·
                refine ⟨427983189173873254873319309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285322126115915503248879539 427983189173873254873319309)
                ·
                  refine ⟨160493695940202470577494741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427983189173873254873319309 160493695940202470577494741)
                  ·
                    refine ⟨3761570998598495404160033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 160493695940202470577494741 3761570998598495404160033)
                    ·
                      refine ⟨2821178248948871553120025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761570998598495404160033 2821178248948871553120025)
                      ·
                        rfl

theorem cell23_5494225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_5494225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494225 prefixEnd_5494225 := by exact prefixLift 5494225
  have htrace : WordTrace (prefixWord ++ tailWord_5494225) baseStart_5494225 baseEnd_5494225 := by
    simpa [prefixWord, tailWord_5494225, baseEnd_5494225] using wordTrace_append hprefix tailTrace_5494225
  have hstable : (prefixWord ++ tailWord_5494225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494225).length < 2 ^ (prefixWord ++ tailWord_5494225).sum := by decide
  have hdescent : baseEnd_5494225 < baseStart_5494225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494245 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5494245 : Nat := 118140960795 + 5494245 * 2 ^ 59
def prefixEnd_5494245 : Nat := 4983230072969 + 3 ^ 40 * 5494245 * 2
def baseEnd_5494245 : Nat := 2821188518561961474869933

theorem tailTrace_5494245 : CollatzResearch.WordTrace tailWord_5494245 prefixEnd_5494245 2821188518561961474869933 := by
  unfold tailWord_5494245
  simp only [CollatzResearch.WordTrace]
  refine ⟨200391577980296182185860189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133594385320197454790573459 200391577980296182185860189)
  ·
    refine ⟨75146841742611068319697571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200391577980296182185860189 75146841742611068319697571)
    ·
      refine ⟨112720262613916602479546357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75146841742611068319697571 112720262613916602479546357)
      ·
        refine ⟨10567524620054681482457471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112720262613916602479546357 10567524620054681482457471)
        ·
          refine ⟨15851286930082022223686207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10567524620054681482457471 15851286930082022223686207)
          ·
            refine ⟨23776930395123033335529311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15851286930082022223686207 23776930395123033335529311)
            ·
              refine ⟨35665395592684550003293967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23776930395123033335529311 35665395592684550003293967)
              ·
                refine ⟨53498093389026825004940951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35665395592684550003293967 53498093389026825004940951)
                ·
                  refine ⟨80247140083540237507411427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53498093389026825004940951 80247140083540237507411427)
                  ·
                    refine ⟨120370710125310356261117141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80247140083540237507411427 120370710125310356261117141)
                    ·
                      refine ⟨2821188518561961474869933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120370710125310356261117141 2821188518561961474869933)
                      ·
                        rfl

theorem cell23_5494245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5494245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494245 prefixEnd_5494245 := by exact prefixLift 5494245
  have htrace : WordTrace (prefixWord ++ tailWord_5494245) baseStart_5494245 baseEnd_5494245 := by
    simpa [prefixWord, tailWord_5494245, baseEnd_5494245] using wordTrace_append hprefix tailTrace_5494245
  have hstable : (prefixWord ++ tailWord_5494245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494245).length < 2 ^ (prefixWord ++ tailWord_5494245).sum := by decide
  have hdescent : baseEnd_5494245 < baseStart_5494245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494250 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_5494250 : Nat := 118140960795 + 5494250 * 2 ^ 59
def prefixEnd_5494250 : Nat := 4983230072969 + 3 ^ 40 * 5494250 * 2
def baseEnd_5494250 : Nat := 2821191085965233955307411

theorem tailTrace_5494250 : CollatzResearch.WordTrace tailWord_5494250 prefixEnd_5494250 2821191085965233955307411 := by
  unfold tailWord_5494250
  simp only [CollatzResearch.WordTrace]
  refine ⟨50097940086319517009948051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133594506896852045359861469 50097940086319517009948051)
  ·
    refine ⟨75146910129479275514922077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50097940086319517009948051 75146910129479275514922077)
    ·
      refine ⟨28180091298554728318095779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75146910129479275514922077 28180091298554728318095779)
      ·
        refine ⟨42270136947832092477143669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28180091298554728318095779 42270136947832092477143669)
        ·
          refine ⟨3962825338859258669732219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42270136947832092477143669 3962825338859258669732219)
          ·
            refine ⟨5944238008288888004598329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962825338859258669732219 5944238008288888004598329)
            ·
              refine ⟨4458178506216666003448747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944238008288888004598329 4458178506216666003448747)
              ·
                refine ⟨6687267759324999005173121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458178506216666003448747 6687267759324999005173121)
                ·
                  refine ⟨5015450819493749253879841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6687267759324999005173121 5015450819493749253879841)
                  ·
                    refine ⟨3761588114620311940409881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5015450819493749253879841 3761588114620311940409881)
                    ·
                      refine ⟨2821191085965233955307411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761588114620311940409881 2821191085965233955307411)
                      ·
                        rfl

theorem cell23_5494250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_5494250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494250 prefixEnd_5494250 := by exact prefixLift 5494250
  have htrace : WordTrace (prefixWord ++ tailWord_5494250) baseStart_5494250 baseEnd_5494250 := by
    simpa [prefixWord, tailWord_5494250, baseEnd_5494250] using wordTrace_append hprefix tailTrace_5494250
  have hstable : (prefixWord ++ tailWord_5494250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494250).length < 2 ^ (prefixWord ++ tailWord_5494250).sum := by decide
  have hdescent : baseEnd_5494250 < baseStart_5494250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494265 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 5, 4]
def baseStart_5494265 : Nat := 118140960795 + 5494265 * 2 ^ 59
def prefixEnd_5494265 : Nat := 4983230072969 + 3 ^ 40 * 5494265 * 2
def baseEnd_5494265 : Nat := 940399596058350465539947

theorem tailTrace_5494265 : CollatzResearch.WordTrace tailWord_5494265 prefixEnd_5494265 940399596058350465539947 := by
  unfold tailWord_5494265
  simp only [CollatzResearch.WordTrace]
  refine ⟨200392307440223725601588249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133594871626815817067725499 200392307440223725601588249)
  ·
    refine ⟨150294230580167794201191187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200392307440223725601588249 150294230580167794201191187)
    ·
      refine ⟨225441345870251691301786781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150294230580167794201191187 225441345870251691301786781)
      ·
        refine ⟨84540504701344384238170043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225441345870251691301786781 84540504701344384238170043)
        ·
          refine ⟨126810757052016576357255065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84540504701344384238170043 126810757052016576357255065)
          ·
            refine ⟨95108067789012432267941299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126810757052016576357255065 95108067789012432267941299)
            ·
              refine ⟨142662101683518648401911949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95108067789012432267941299 142662101683518648401911949)
              ·
                refine ⟨53498288131319493150716981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142662101683518648401911949 53498288131319493150716981)
                ·
                  refine ⟨5015464512311202482879717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53498288131319493150716981 5015464512311202482879717)
                  ·
                    refine ⟨940399596058350465539947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015464512311202482879717 940399596058350465539947)
                    ·
                      rfl

theorem cell23_5494265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_5494265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494265 prefixEnd_5494265 := by exact prefixLift 5494265
  have htrace : WordTrace (prefixWord ++ tailWord_5494265) baseStart_5494265 baseEnd_5494265 := by
    simpa [prefixWord, tailWord_5494265, baseEnd_5494265] using wordTrace_append hprefix tailTrace_5494265
  have hstable : (prefixWord ++ tailWord_5494265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494265).length < 2 ^ (prefixWord ++ tailWord_5494265).sum := by decide
  have hdescent : baseEnd_5494265 < baseStart_5494265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494288 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_5494288 : Nat := 118140960795 + 5494288 * 2 ^ 59
def prefixEnd_5494288 : Nat := 4983230072969 + 3 ^ 40 * 5494288 * 2
def baseEnd_5494288 : Nat := 2821210598230104806632235

theorem tailTrace_5494288 : CollatzResearch.WordTrace tailWord_5494288 prefixEnd_5494288 2821210598230104806632235 := by
  unfold tailWord_5494288
  simp only [CollatzResearch.WordTrace]
  refine ⟨100196573159570200264837759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133595430879426933686450345 100196573159570200264837759)
  ·
    refine ⟨150294859739355300397256639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100196573159570200264837759 150294859739355300397256639)
    ·
      refine ⟨225442289609032950595884959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150294859739355300397256639 225442289609032950595884959)
      ·
        refine ⟨338163434413549425893827439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225442289609032950595884959 338163434413549425893827439)
        ·
          refine ⟨507245151620324138840741159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338163434413549425893827439 507245151620324138840741159)
          ·
            refine ⟨760867727430486208261111739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507245151620324138840741159 760867727430486208261111739)
            ·
              refine ⟨1141301591145729312391667609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760867727430486208261111739 1141301591145729312391667609)
              ·
                refine ⟨855976193359296984293750707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141301591145729312391667609 855976193359296984293750707)
                ·
                  refine ⟨1283964290038945476440626061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855976193359296984293750707 1283964290038945476440626061)
                  ·
                    refine ⟨481486608764604553665234773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283964290038945476440626061 481486608764604553665234773)
                    ·
                      refine ⟨2821210598230104806632235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 481486608764604553665234773 2821210598230104806632235)
                      ·
                        rfl

theorem cell23_5494288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_5494288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494288 prefixEnd_5494288 := by exact prefixLift 5494288
  have htrace : WordTrace (prefixWord ++ tailWord_5494288) baseStart_5494288 baseEnd_5494288 := by
    simpa [prefixWord, tailWord_5494288, baseEnd_5494288] using wordTrace_append hprefix tailTrace_5494288
  have hstable : (prefixWord ++ tailWord_5494288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494288).length < 2 ^ (prefixWord ++ tailWord_5494288).sum := by decide
  have hdescent : baseEnd_5494288 < baseStart_5494288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494356 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_5494356 : Nat := 118140960795 + 5494356 * 2 ^ 59
def prefixEnd_5494356 : Nat := 4983230072969 + 3 ^ 40 * 5494356 * 2
def baseEnd_5494356 : Nat := 2821245514914610540581923

theorem tailTrace_5494356 : CollatzResearch.WordTrace tailWord_5494356 prefixEnd_5494356 2821245514914610540581923 := by
  unfold tailWord_5494356
  simp only [CollatzResearch.WordTrace]
  refine ⟨100197813241447024071575461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133597084321929365428767281 100197813241447024071575461)
  ·
    refine ⟨18787089982771317013420399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100197813241447024071575461 18787089982771317013420399)
    ·
      refine ⟨28180634974156975520130599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18787089982771317013420399 28180634974156975520130599)
      ·
        refine ⟨42270952461235463280195899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28180634974156975520130599 42270952461235463280195899)
        ·
          refine ⟨63406428691853194920293849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42270952461235463280195899 63406428691853194920293849)
          ·
            refine ⟨47554821518889896190220387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63406428691853194920293849 47554821518889896190220387)
            ·
              refine ⟨71332232278334844285330581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47554821518889896190220387 71332232278334844285330581)
              ·
                refine ⟨3343698388046945825874871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71332232278334844285330581 3343698388046945825874871)
                ·
                  refine ⟨5015547582070418738812307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343698388046945825874871 5015547582070418738812307)
                  ·
                    refine ⟨7523321373105628108218461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5015547582070418738812307 7523321373105628108218461)
                    ·
                      refine ⟨2821245514914610540581923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7523321373105628108218461 2821245514914610540581923)
                      ·
                        rfl

theorem cell23_5494356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_5494356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494356 prefixEnd_5494356 := by exact prefixLift 5494356
  have htrace : WordTrace (prefixWord ++ tailWord_5494356) baseStart_5494356 baseEnd_5494356 := by
    simpa [prefixWord, tailWord_5494356, baseEnd_5494356] using wordTrace_append hprefix tailTrace_5494356
  have hstable : (prefixWord ++ tailWord_5494356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494356).length < 2 ^ (prefixWord ++ tailWord_5494356).sum := by decide
  have hdescent : baseEnd_5494356 < baseStart_5494356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494372 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_5494372 : Nat := 118140960795 + 5494372 * 2 ^ 59
def prefixEnd_5494372 : Nat := 4983230072969 + 3 ^ 40 * 5494372 * 2
def baseEnd_5494372 : Nat := 940417910201694159327283

theorem tailTrace_5494372 : CollatzResearch.WordTrace tailWord_5494372 prefixEnd_5494372 940417910201694159327283 := by
  unfold tailWord_5494372
  simp only [CollatzResearch.WordTrace]
  refine ⟨100198105025418041437866685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133597473367224055250488913 100198105025418041437866685)
  ·
    refine ⟨37574289384531765539200007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100198105025418041437866685 37574289384531765539200007)
    ·
      refine ⟨56361434076797648308800011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37574289384531765539200007 56361434076797648308800011)
      ·
        refine ⟨84542151115196472463200017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56361434076797648308800011 84542151115196472463200017)
        ·
          refine ⟨63406613336397354347400013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84542151115196472463200017 63406613336397354347400013)
          ·
            refine ⟨23777480001149007880275005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63406613336397354347400013 23777480001149007880275005)
            ·
              refine ⟨8916555000430877955103127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23777480001149007880275005 8916555000430877955103127)
              ·
                refine ⟨13374832500646316932654691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8916555000430877955103127 13374832500646316932654691)
                ·
                  refine ⟨20062248750969475398982037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13374832500646316932654691 20062248750969475398982037)
                  ·
                    refine ⟨940417910201694159327283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20062248750969475398982037 940417910201694159327283)
                    ·
                      rfl

theorem cell23_5494372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_5494372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494372 prefixEnd_5494372 := by exact prefixLift 5494372
  have htrace : WordTrace (prefixWord ++ tailWord_5494372) baseStart_5494372 baseEnd_5494372 := by
    simpa [prefixWord, tailWord_5494372, baseEnd_5494372] using wordTrace_append hprefix tailTrace_5494372
  have hstable : (prefixWord ++ tailWord_5494372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494372).length < 2 ^ (prefixWord ++ tailWord_5494372).sum := by decide
  have hdescent : baseEnd_5494372 < baseStart_5494372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494389 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5494389 : Nat := 118140960795 + 5494389 * 2 ^ 59
def prefixEnd_5494389 : Nat := 4983230072969 + 3 ^ 40 * 5494389 * 2
def baseEnd_5494389 : Nat := 940420819925402970489757

theorem tailTrace_5494389 : CollatzResearch.WordTrace tailWord_5494389 prefixEnd_5494389 940420819925402970489757 := by
  unfold tailWord_5494389
  simp only [CollatzResearch.WordTrace]
  refine ⟨200396830091774494779102221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133597886727849663186068147 200396830091774494779102221)
  ·
    refine ⟨75148811284415435542163333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200396830091774494779102221 75148811284415435542163333)
    ·
      refine ⟨14090402115827894164155625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75148811284415435542163333 14090402115827894164155625)
      ·
        refine ⟨10567801586870920623116719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14090402115827894164155625 10567801586870920623116719)
        ·
          refine ⟨15851702380306380934675079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10567801586870920623116719 15851702380306380934675079)
          ·
            refine ⟨23777553570459571402012619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15851702380306380934675079 23777553570459571402012619)
            ·
              refine ⟨35666330355689357103018929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23777553570459571402012619 35666330355689357103018929)
              ·
                refine ⟨26749747766767017827264197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35666330355689357103018929 26749747766767017827264197)
                ·
                  refine ⟨5015577706268815842612037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26749747766767017827264197 5015577706268815842612037)
                  ·
                    refine ⟨940420819925402970489757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015577706268815842612037 940420819925402970489757)
                    ·
                      rfl

theorem cell23_5494389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5494389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494389 prefixEnd_5494389 := by exact prefixLift 5494389
  have htrace : WordTrace (prefixWord ++ tailWord_5494389) baseStart_5494389 baseEnd_5494389 := by
    simpa [prefixWord, tailWord_5494389, baseEnd_5494389] using wordTrace_append hprefix tailTrace_5494389
  have hstable : (prefixWord ++ tailWord_5494389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494389).length < 2 ^ (prefixWord ++ tailWord_5494389).sum := by decide
  have hdescent : baseEnd_5494389 < baseStart_5494389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494390 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5494390 : Nat := 118140960795 + 5494390 * 2 ^ 59
def prefixEnd_5494390 : Nat := 4983230072969 + 3 ^ 40 * 5494390 * 2
def baseEnd_5494390 : Nat := 2821262973256863407556767

theorem tailTrace_5494390 : CollatzResearch.WordTrace tailWord_5494390 prefixEnd_5494390 2821262973256863407556767 := by
  unfold tailWord_5494390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524804160298179496868039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133597911043180581299925749 12524804160298179496868039)
  ·
    refine ⟨18787206240447269245302059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12524804160298179496868039 18787206240447269245302059)
    ·
      refine ⟨28180809360670903867953089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18787206240447269245302059 28180809360670903867953089)
      ·
        refine ⟨21135607020503177900964817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28180809360670903867953089 21135607020503177900964817)
        ·
          refine ⟨15851705265377383425723613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21135607020503177900964817 15851705265377383425723613)
          ·
            refine ⟨5944389474516518784646355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15851705265377383425723613 5944389474516518784646355)
            ·
              refine ⟨8916584211774778176969533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944389474516518784646355 8916584211774778176969533)
              ·
                refine ⟨3343719079415541816363575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8916584211774778176969533 3343719079415541816363575)
                ·
                  refine ⟨5015578619123312724545363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343719079415541816363575 5015578619123312724545363)
                  ·
                    refine ⟨7523367928684969086818045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5015578619123312724545363 7523367928684969086818045)
                    ·
                      refine ⟨2821262973256863407556767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7523367928684969086818045 2821262973256863407556767)
                      ·
                        rfl

theorem cell23_5494390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5494390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494390 prefixEnd_5494390 := by exact prefixLift 5494390
  have htrace : WordTrace (prefixWord ++ tailWord_5494390) baseStart_5494390 baseEnd_5494390 := by
    simpa [prefixWord, tailWord_5494390, baseEnd_5494390] using wordTrace_append hprefix tailTrace_5494390
  have hstable : (prefixWord ++ tailWord_5494390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494390).length < 2 ^ (prefixWord ++ tailWord_5494390).sum := by decide
  have hdescent : baseEnd_5494390 < baseStart_5494390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494425 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_5494425 : Nat := 118140960795 + 5494425 * 2 ^ 59
def prefixEnd_5494425 : Nat := 4983230072969 + 3 ^ 40 * 5494425 * 2
def baseEnd_5494425 : Nat := 2821280945079770770619105

theorem tailTrace_5494425 : CollatzResearch.WordTrace tailWord_5494425 prefixEnd_5494425 2821280945079770770619105 := by
  unfold tailWord_5494425
  simp only [CollatzResearch.WordTrace]
  refine ⟨200398143119644072927412729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133598762079762715284941819 200398143119644072927412729)
  ·
    refine ⟨150298607339733054695559547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200398143119644072927412729 150298607339733054695559547)
    ·
      refine ⟨225447911009599582043339321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150298607339733054695559547 225447911009599582043339321)
      ·
        refine ⟨169085933257199686532504491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225447911009599582043339321 169085933257199686532504491)
        ·
          refine ⟨253628899885799529798756737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169085933257199686532504491 253628899885799529798756737)
          ·
            refine ⟨190221674914349647349067553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253628899885799529798756737 190221674914349647349067553)
            ·
              refine ⟨142666256185762235511800665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190221674914349647349067553 142666256185762235511800665)
              ·
                refine ⟨106999692139321676633850499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142666256185762235511800665 106999692139321676633850499)
                ·
                  refine ⟨160499538208982514950775749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106999692139321676633850499 160499538208982514950775749)
                  ·
                    refine ⟨30093663414184221553270453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160499538208982514950775749 30093663414184221553270453)
                    ·
                      refine ⟨2821280945079770770619105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30093663414184221553270453 2821280945079770770619105)
                      ·
                        rfl

theorem cell23_5494425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_5494425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494425 prefixEnd_5494425 := by exact prefixLift 5494425
  have htrace : WordTrace (prefixWord ++ tailWord_5494425) baseStart_5494425 baseEnd_5494425 := by
    simpa [prefixWord, tailWord_5494425, baseEnd_5494425] using wordTrace_append hprefix tailTrace_5494425
  have hstable : (prefixWord ++ tailWord_5494425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494425).length < 2 ^ (prefixWord ++ tailWord_5494425).sum := by decide
  have hdescent : baseEnd_5494425 < baseStart_5494425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494472 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_5494472 : Nat := 118140960795 + 5494472 * 2 ^ 59
def prefixEnd_5494472 : Nat := 4983230072969 + 3 ^ 40 * 5494472 * 2
def baseEnd_5494472 : Nat := 2821305078670532086731389

theorem tailTrace_5494472 : CollatzResearch.WordTrace tailWord_5494472 prefixEnd_5494472 2821305078670532086731389 := by
  unfold tailWord_5494472
  simp only [CollatzResearch.WordTrace]
  refine ⟨100199928675236899977186835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133599904900315866636249113 100199928675236899977186835)
  ·
    refine ⟨150299893012855349965780253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100199928675236899977186835 150299893012855349965780253)
    ·
      refine ⟨56362459879820756237167595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150299893012855349965780253 56362459879820756237167595)
      ·
        refine ⟨84543689819731134355751393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56362459879820756237167595 84543689819731134355751393)
        ·
          refine ⟨63407767364798350766813545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84543689819731134355751393 63407767364798350766813545)
          ·
            refine ⟨47555825523598763075110159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63407767364798350766813545 47555825523598763075110159)
            ·
              refine ⟨71333738285398144612665239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47555825523598763075110159 71333738285398144612665239)
              ·
                refine ⟨107000607428097216918997859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71333738285398144612665239 107000607428097216918997859)
                ·
                  refine ⟨160500911142145825378496789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107000607428097216918997859 160500911142145825378496789)
                  ·
                    refine ⟨7523480209788085564617037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160500911142145825378496789 7523480209788085564617037)
                    ·
                      refine ⟨2821305078670532086731389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7523480209788085564617037 2821305078670532086731389)
                      ·
                        rfl

theorem cell23_5494472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_5494472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494472 prefixEnd_5494472 := by exact prefixLift 5494472
  have htrace : WordTrace (prefixWord ++ tailWord_5494472) baseStart_5494472 baseEnd_5494472 := by
    simpa [prefixWord, tailWord_5494472, baseEnd_5494472] using wordTrace_append hprefix tailTrace_5494472
  have hstable : (prefixWord ++ tailWord_5494472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494472).length < 2 ^ (prefixWord ++ tailWord_5494472).sum := by decide
  have hdescent : baseEnd_5494472 < baseStart_5494472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494475 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 11]
def baseStart_5494475 : Nat := 118140960795 + 5494475 * 2 ^ 59
def prefixEnd_5494475 : Nat := 4983230072969 + 3 ^ 40 * 5494475 * 2
def baseEnd_5494475 : Nat := 313478513234721730554875

theorem tailTrace_5494475 : CollatzResearch.WordTrace tailWord_5494475 prefixEnd_5494475 313478513234721730554875 := by
  unfold tailWord_5494475
  simp only [CollatzResearch.WordTrace]
  refine ⟨200399966769462931466732879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133599977846308620977821919 200399966769462931466732879)
  ·
    refine ⟨300599950154194397200099319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200399966769462931466732879 300599950154194397200099319)
    ·
      refine ⟨450899925231291595800148979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300599950154194397200099319 450899925231291595800148979)
      ·
        refine ⟨676349887846937393700223469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450899925231291595800148979 676349887846937393700223469)
        ·
          refine ⟨253631207942601522637583801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 676349887846937393700223469 253631207942601522637583801)
          ·
            refine ⟨190223405956951141978187851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253631207942601522637583801 190223405956951141978187851)
            ·
              refine ⟨285335108935426712967281777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190223405956951141978187851 285335108935426712967281777)
              ·
                refine ⟨214001331701570034725461333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285335108935426712967281777 214001331701570034725461333)
                ·
                  refine ⟨313478513234721730554875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 214001331701570034725461333 313478513234721730554875)
                  ·
                    rfl

theorem cell23_5494475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 11].length) (baseStart_5494475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494475 prefixEnd_5494475 := by exact prefixLift 5494475
  have htrace : WordTrace (prefixWord ++ tailWord_5494475) baseStart_5494475 baseEnd_5494475 := by
    simpa [prefixWord, tailWord_5494475, baseEnd_5494475] using wordTrace_append hprefix tailTrace_5494475
  have hstable : (prefixWord ++ tailWord_5494475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494475).length < 2 ^ (prefixWord ++ tailWord_5494475).sum := by decide
  have hdescent : baseEnd_5494475 < baseStart_5494475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494522 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_5494522 : Nat := 118140960795 + 5494522 * 2 ^ 59
def prefixEnd_5494522 : Nat := 4983230072969 + 3 ^ 40 * 5494522 * 2
def baseEnd_5494522 : Nat := 940443584234418963702053

theorem tailTrace_5494522 : CollatzResearch.WordTrace tailWord_5494522 prefixEnd_5494522 940443584234418963702053 := by
  unfold tailWord_5494522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50100420250073164623423455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133601120666861772329129213 50100420250073164623423455)
  ·
    refine ⟨75150630375109746935135183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50100420250073164623423455 75150630375109746935135183)
    ·
      refine ⟨112725945562664620402702775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75150630375109746935135183 112725945562664620402702775)
      ·
        refine ⟨169088918343996930604054163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112725945562664620402702775 169088918343996930604054163)
        ·
          refine ⟨253633377515995395906081245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169088918343996930604054163 253633377515995395906081245)
          ·
            refine ⟨95112516568498273464780467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253633377515995395906081245 95112516568498273464780467)
            ·
              refine ⟨142668774852747410197170701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95112516568498273464780467 142668774852747410197170701)
              ·
                refine ⟨53500790569780278823939013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142668774852747410197170701 53500790569780278823939013)
                ·
                  refine ⟨10031398231833802279488565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53500790569780278823939013 10031398231833802279488565)
                  ·
                    refine ⟨940443584234418963702053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10031398231833802279488565 940443584234418963702053)
                    ·
                      rfl

theorem cell23_5494522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_5494522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494522 prefixEnd_5494522 := by exact prefixLift 5494522
  have htrace : WordTrace (prefixWord ++ tailWord_5494522) baseStart_5494522 baseEnd_5494522 := by
    simpa [prefixWord, tailWord_5494522, baseEnd_5494522] using wordTrace_append hprefix tailTrace_5494522
  have hstable : (prefixWord ++ tailWord_5494522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494522).length < 2 ^ (prefixWord ++ tailWord_5494522).sum := by decide
  have hdescent : baseEnd_5494522 < baseStart_5494522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494526 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_5494526 : Nat := 118140960795 + 5494526 * 2 ^ 59
def prefixEnd_5494526 : Nat := 4983230072969 + 3 ^ 40 * 5494526 * 2
def baseEnd_5494526 : Nat := 313481422958430541717349

theorem tailTrace_5494526 : CollatzResearch.WordTrace tailWord_5494526 prefixEnd_5494526 313481422958430541717349 := by
  unfold tailWord_5494526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25050228361534770897104929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133601217928185444784559621 25050228361534770897104929)
  ·
    refine ⟨18787671271151078172828697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25050228361534770897104929 18787671271151078172828697)
    ·
      refine ⟨14090753453363308629621523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18787671271151078172828697 14090753453363308629621523)
      ·
        refine ⟨21136130180044962944432285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14090753453363308629621523 21136130180044962944432285)
        ·
          refine ⟨7926048817516861104162107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21136130180044962944432285 7926048817516861104162107)
          ·
            refine ⟨11889073226275291656243161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926048817516861104162107 11889073226275291656243161)
            ·
              refine ⟨8916804919706468742182371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11889073226275291656243161 8916804919706468742182371)
              ·
                refine ⟨13375207379559703113273557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8916804919706468742182371 13375207379559703113273557)
                ·
                  refine ⟨313481422958430541717349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13375207379559703113273557 313481422958430541717349)
                  ·
                    rfl

theorem cell23_5494526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_5494526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494526 prefixEnd_5494526 := by exact prefixLift 5494526
  have htrace : WordTrace (prefixWord ++ tailWord_5494526) baseStart_5494526 baseEnd_5494526 := by
    simpa [prefixWord, tailWord_5494526, baseEnd_5494526] using wordTrace_append hprefix tailTrace_5494526
  have hstable : (prefixWord ++ tailWord_5494526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494526).length < 2 ^ (prefixWord ++ tailWord_5494526).sum := by decide
  have hdescent : baseEnd_5494526 < baseStart_5494526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494529 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_5494529 : Nat := 118140960795 + 5494529 * 2 ^ 59
def prefixEnd_5494529 : Nat := 4983230072969 + 3 ^ 40 * 5494529 * 2
def baseEnd_5494529 : Nat := 2821334347067838363718627

theorem tailTrace_5494529 : CollatzResearch.WordTrace tailWord_5494529 prefixEnd_5494529 2821334347067838363718627 := by
  unfold tailWord_5494529
  simp only [CollatzResearch.WordTrace]
  refine ⟨200401936311267298689198641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133601290874178199126132427 200401936311267298689198641)
  ·
    refine ⟨150301452233450474016898981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200401936311267298689198641 150301452233450474016898981)
    ·
      refine ⟨28181522293771963878168559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150301452233450474016898981 28181522293771963878168559)
      ·
        refine ⟨42272283440657945817252839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28181522293771963878168559 42272283440657945817252839)
        ·
          refine ⟨63408425160986918725879259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42272283440657945817252839 63408425160986918725879259)
          ·
            refine ⟨95112637741480378088818889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63408425160986918725879259 95112637741480378088818889)
            ·
              refine ⟨71334478306110283566614167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95112637741480378088818889 71334478306110283566614167)
              ·
                refine ⟨107001717459165425349921251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71334478306110283566614167 107001717459165425349921251)
                ·
                  refine ⟨160502576188748138024881877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107001717459165425349921251 160502576188748138024881877)
                  ·
                    refine ⟨3761779129423784484958169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 160502576188748138024881877 3761779129423784484958169)
                    ·
                      refine ⟨2821334347067838363718627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761779129423784484958169 2821334347067838363718627)
                      ·
                        rfl

theorem cell23_5494529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_5494529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494529 prefixEnd_5494529 := by exact prefixLift 5494529
  have htrace : WordTrace (prefixWord ++ tailWord_5494529) baseStart_5494529 baseEnd_5494529 := by
    simpa [prefixWord, tailWord_5494529, baseEnd_5494529] using wordTrace_append hprefix tailTrace_5494529
  have hstable : (prefixWord ++ tailWord_5494529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494529).length < 2 ^ (prefixWord ++ tailWord_5494529).sum := by decide
  have hdescent : baseEnd_5494529 < baseStart_5494529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494559 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_5494559 : Nat := 118140960795 + 5494559 * 2 ^ 59
def prefixEnd_5494559 : Nat := 4983230072969 + 3 ^ 40 * 5494559 * 2
def baseEnd_5494559 : Nat := 2821349751487473246343489

theorem tailTrace_5494559 : CollatzResearch.WordTrace tailWord_5494559 prefixEnd_5494559 2821349751487473246343489 := by
  unfold tailWord_5494559
  simp only [CollatzResearch.WordTrace]
  refine ⟨200403030501158613812790731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133602020334105742541860487 200403030501158613812790731)
  ·
    refine ⟨300604545751737920719186097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200403030501158613812790731 300604545751737920719186097)
    ·
      refine ⟨225453409313803440539389573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300604545751737920719186097 225453409313803440539389573)
      ·
        refine ⟨42272514246338145101135545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225453409313803440539389573 42272514246338145101135545)
        ·
          refine ⟨31704385684753608825851659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42272514246338145101135545 31704385684753608825851659)
          ·
            refine ⟨47556578527130413238777489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31704385684753608825851659 47556578527130413238777489)
            ·
              refine ⟨35667433895347809929083117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47556578527130413238777489 35667433895347809929083117)
              ·
                refine ⟨13375287710755428723406169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35667433895347809929083117 13375287710755428723406169)
                ·
                  refine ⟨10031465783066571542554627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13375287710755428723406169 10031465783066571542554627)
                  ·
                    refine ⟨15047198674599857313831941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10031465783066571542554627 15047198674599857313831941)
                    ·
                      refine ⟨2821349751487473246343489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15047198674599857313831941 2821349751487473246343489)
                      ·
                        rfl

theorem cell23_5494559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_5494559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494559 prefixEnd_5494559 := by exact prefixLift 5494559
  have htrace : WordTrace (prefixWord ++ tailWord_5494559) baseStart_5494559 baseEnd_5494559 := by
    simpa [prefixWord, tailWord_5494559, baseEnd_5494559] using wordTrace_append hprefix tailTrace_5494559
  have hstable : (prefixWord ++ tailWord_5494559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494559).length < 2 ^ (prefixWord ++ tailWord_5494559).sum := by decide
  have hdescent : baseEnd_5494559 < baseStart_5494559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494586 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_5494586 : Nat := 118140960795 + 5494586 * 2 ^ 59
def prefixEnd_5494586 : Nat := 4983230072969 + 3 ^ 40 * 5494586 * 2
def baseEnd_5494586 : Nat := 940454538488381546901955

theorem tailTrace_5494586 : CollatzResearch.WordTrace tailWord_5494586 prefixEnd_5494586 940454538488381546901955 := by
  unfold tailWord_5494586
  simp only [CollatzResearch.WordTrace]
  refine ⟨50101003818015199356005903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133602676848040531616015741 50101003818015199356005903)
  ·
    refine ⟨75151505727022799034008855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50101003818015199356005903 75151505727022799034008855)
    ·
      refine ⟨112727258590534198551013283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75151505727022799034008855 112727258590534198551013283)
      ·
        refine ⟨169090887885801297826519925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112727258590534198551013283 169090887885801297826519925)
        ·
          refine ⟨15852270739293871671236243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169090887885801297826519925 15852270739293871671236243)
          ·
            refine ⟨23778406108940807506854365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15852270739293871671236243 23778406108940807506854365)
            ·
              refine ⟨8916902290852802815070387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23778406108940807506854365 8916902290852802815070387)
              ·
                refine ⟨13375353436279204222605581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8916902290852802815070387 13375353436279204222605581)
                ·
                  refine ⟨5015757538604701583477093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13375353436279204222605581 5015757538604701583477093)
                  ·
                    refine ⟨940454538488381546901955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015757538604701583477093 940454538488381546901955)
                    ·
                      rfl

theorem cell23_5494586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_5494586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494586 prefixEnd_5494586 := by exact prefixLift 5494586
  have htrace : WordTrace (prefixWord ++ tailWord_5494586) baseStart_5494586 baseEnd_5494586 := by
    simpa [prefixWord, tailWord_5494586, baseEnd_5494586] using wordTrace_append hprefix tailTrace_5494586
  have hstable : (prefixWord ++ tailWord_5494586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494586).length < 2 ^ (prefixWord ++ tailWord_5494586).sum := by decide
  have hdescent : baseEnd_5494586 < baseStart_5494586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494649 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_5494649 : Nat := 118140960795 + 5494649 * 2 ^ 59
def prefixEnd_5494649 : Nat := 4983230072969 + 3 ^ 40 * 5494649 * 2
def baseEnd_5494649 : Nat := 2821395964746377894218075

theorem tailTrace_5494649 : CollatzResearch.WordTrace tailWord_5494649 prefixEnd_5494649 2821395964746377894218075 := by
  unfold tailWord_5494649
  simp only [CollatzResearch.WordTrace]
  refine ⟨200406313070832559183567001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133604208713888372789044667 200406313070832559183567001)
  ·
    refine ⟨150304734803124419387675251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200406313070832559183567001 150304734803124419387675251)
    ·
      refine ⟨225457102204686629081512877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150304734803124419387675251 225457102204686629081512877)
      ·
        refine ⟨84546413326757485905567329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225457102204686629081512877 84546413326757485905567329)
        ·
          refine ⟨63409809995068114429175497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84546413326757485905567329 63409809995068114429175497)
          ·
            refine ⟨47557357496301085821881623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63409809995068114429175497 47557357496301085821881623)
            ·
              refine ⟨71336036244451628732822435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47557357496301085821881623 71336036244451628732822435)
              ·
                refine ⟨107004054366677443099233653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71336036244451628732822435 107004054366677443099233653)
                ·
                  refine ⟨10031630096876010290553155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107004054366677443099233653 10031630096876010290553155)
                  ·
                    refine ⟨15047445145314015435829733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10031630096876010290553155 15047445145314015435829733)
                    ·
                      refine ⟨2821395964746377894218075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15047445145314015435829733 2821395964746377894218075)
                      ·
                        rfl

theorem cell23_5494649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_5494649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494649 prefixEnd_5494649 := by exact prefixLift 5494649
  have htrace : WordTrace (prefixWord ++ tailWord_5494649) baseStart_5494649 baseEnd_5494649 := by
    simpa [prefixWord, tailWord_5494649, baseEnd_5494649] using wordTrace_append hprefix tailTrace_5494649
  have hstable : (prefixWord ++ tailWord_5494649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494649).length < 2 ^ (prefixWord ++ tailWord_5494649).sum := by decide
  have hdescent : baseEnd_5494649 < baseStart_5494649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494659 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 1, 6]
def baseStart_5494659 : Nat := 118140960795 + 5494659 * 2 ^ 59
def prefixEnd_5494659 : Nat := 4983230072969 + 3 ^ 40 * 5494659 * 2
def baseEnd_5494659 : Nat := 940467033184307618364343

theorem tailTrace_5494659 : CollatzResearch.WordTrace tailWord_5494659 prefixEnd_5494659 940467033184307618364343 := by
  unfold tailWord_5494659
  simp only [CollatzResearch.WordTrace]
  refine ⟨200406677800796330891431031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133604451867197553927620687 200406677800796330891431031)
  ·
    refine ⟨300610016701194496337146547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200406677800796330891431031 300610016701194496337146547)
    ·
      refine ⟨450915025051791744505719821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300610016701194496337146547 450915025051791744505719821)
      ·
        refine ⟨169093134394421904189644933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450915025051791744505719821 169093134394421904189644933)
        ·
          refine ⟨31704962698954107035558425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169093134394421904189644933 31704962698954107035558425)
          ·
            refine ⟨23778722024215580276668819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31704962698954107035558425 23778722024215580276668819)
            ·
              refine ⟨35668083036323370415003229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23778722024215580276668819 35668083036323370415003229)
              ·
                refine ⟨13375531138621263905626211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35668083036323370415003229 13375531138621263905626211)
                ·
                  refine ⟨20063296707931895858439317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13375531138621263905626211 20063296707931895858439317)
                  ·
                    refine ⟨940467033184307618364343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20063296707931895858439317 940467033184307618364343)
                    ·
                      rfl

theorem cell23_5494659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 6].length) (baseStart_5494659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494659 prefixEnd_5494659 := by exact prefixLift 5494659
  have htrace : WordTrace (prefixWord ++ tailWord_5494659) baseStart_5494659 baseEnd_5494659 := by
    simpa [prefixWord, tailWord_5494659, baseEnd_5494659] using wordTrace_append hprefix tailTrace_5494659
  have hstable : (prefixWord ++ tailWord_5494659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494659).length < 2 ^ (prefixWord ++ tailWord_5494659).sum := by decide
  have hdescent : baseEnd_5494659 < baseStart_5494659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494670 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5494670 : Nat := 118140960795 + 5494670 * 2 ^ 59
def prefixEnd_5494670 : Nat := 4983230072969 + 3 ^ 40 * 5494670 * 2
def baseEnd_5494670 : Nat := 2821406747840122312055479

theorem tailTrace_5494670 : CollatzResearch.WordTrace tailWord_5494670 prefixEnd_5494670 2821406747840122312055479 := by
  unfold tailWord_5494670
  simp only [CollatzResearch.WordTrace]
  refine ⟨25050884875469559971260183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133604719335837653180054309 25050884875469559971260183)
  ·
    refine ⟨37576327313204339956890275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25050884875469559971260183 37576327313204339956890275)
    ·
      refine ⟨56364490969806509935335413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37576327313204339956890275 56364490969806509935335413)
      ·
        refine ⟨5284171028419360306437695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56364490969806509935335413 5284171028419360306437695)
        ·
          refine ⟨7926256542629040459656543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284171028419360306437695 7926256542629040459656543)
          ·
            refine ⟨11889384813943560689484815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926256542629040459656543 11889384813943560689484815)
            ·
              refine ⟨17834077220915341034227223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11889384813943560689484815 17834077220915341034227223)
              ·
                refine ⟨26751115831373011551340835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17834077220915341034227223 26751115831373011551340835)
                ·
                  refine ⟨40126673747059517327011253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26751115831373011551340835 40126673747059517327011253)
                  ·
                    refine ⟨3761875663786829749407305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40126673747059517327011253 3761875663786829749407305)
                    ·
                      refine ⟨2821406747840122312055479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761875663786829749407305 2821406747840122312055479)
                      ·
                        rfl

theorem cell23_5494670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5494670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494670 prefixEnd_5494670 := by exact prefixLift 5494670
  have htrace : WordTrace (prefixWord ++ tailWord_5494670) baseStart_5494670 baseEnd_5494670 := by
    simpa [prefixWord, tailWord_5494670, baseEnd_5494670] using wordTrace_append hprefix tailTrace_5494670
  have hstable : (prefixWord ++ tailWord_5494670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494670).length < 2 ^ (prefixWord ++ tailWord_5494670).sum := by decide
  have hdescent : baseEnd_5494670 < baseStart_5494670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494676 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_5494676 : Nat := 118140960795 + 5494676 * 2 ^ 59
def prefixEnd_5494676 : Nat := 4983230072969 + 3 ^ 40 * 5494676 * 2
def baseEnd_5494676 : Nat := 940469942908016429526817

theorem tailTrace_5494676 : CollatzResearch.WordTrace tailWord_5494676 prefixEnd_5494676 940469942908016429526817 := by
  unfold tailWord_5494676
  simp only [CollatzResearch.WordTrace]
  refine ⟨100203648920867371397399941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133604865227823161863199921 100203648920867371397399941)
  ·
    refine ⟨18788184172662632137012489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100203648920867371397399941 18788184172662632137012489)
    ·
      refine ⟨14091138129496974102759367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18788184172662632137012489 14091138129496974102759367)
      ·
        refine ⟨21136707194245461154139051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14091138129496974102759367 21136707194245461154139051)
        ·
          refine ⟨31705060791368191731208577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21136707194245461154139051 31705060791368191731208577)
          ·
            refine ⟨23778795593526143798406433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31705060791368191731208577 23778795593526143798406433)
            ·
              refine ⟨17834096695144607848804825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23778795593526143798406433 17834096695144607848804825)
              ·
                refine ⟨13375572521358455886603619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17834096695144607848804825 13375572521358455886603619)
                ·
                  refine ⟨20063358782037683829905429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13375572521358455886603619 20063358782037683829905429)
                  ·
                    refine ⟨940469942908016429526817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20063358782037683829905429 940469942908016429526817)
                    ·
                      rfl

theorem cell23_5494676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_5494676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494676 prefixEnd_5494676 := by exact prefixLift 5494676
  have htrace : WordTrace (prefixWord ++ tailWord_5494676) baseStart_5494676 baseEnd_5494676 := by
    simpa [prefixWord, tailWord_5494676, baseEnd_5494676] using wordTrace_append hprefix tailTrace_5494676
  have hstable : (prefixWord ++ tailWord_5494676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494676).length < 2 ^ (prefixWord ++ tailWord_5494676).sum := by decide
  have hdescent : baseEnd_5494676 < baseStart_5494676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494743 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 1, 3, 2]
def baseStart_5494743 : Nat := 118140960795 + 5494743 * 2 ^ 59
def prefixEnd_5494743 : Nat := 4983230072969 + 3 ^ 40 * 5494743 * 2
def baseEnd_5494743 : Nat := 2821444231927900526442643

theorem tailTrace_5494743 : CollatzResearch.WordTrace tailWord_5494743 prefixEnd_5494743 2821444231927900526442643 := by
  unfold tailWord_5494743
  simp only [CollatzResearch.WordTrace]
  refine ⟨200409741532492013237488883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133606494354994675491659255 200409741532492013237488883)
  ·
    refine ⟨300614612298738019856233325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200409741532492013237488883 300614612298738019856233325)
    ·
      refine ⟨112730479612026757446087497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300614612298738019856233325 112730479612026757446087497)
      ·
        refine ⟨84547859709020068084565623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112730479612026757446087497 84547859709020068084565623)
        ·
          refine ⟨126821789563530102126848435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84547859709020068084565623 126821789563530102126848435)
          ·
            refine ⟨190232684345295153190272653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126821789563530102126848435 190232684345295153190272653)
            ·
              refine ⟨71337256629485682446352245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190232684345295153190272653 71337256629485682446352245)
              ·
                refine ⟨6687867809014282729345523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71337256629485682446352245 6687867809014282729345523)
                ·
                  refine ⟨10031801713521424094018285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687867809014282729345523 10031801713521424094018285)
                  ·
                    refine ⟨3761925642570534035256857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10031801713521424094018285 3761925642570534035256857)
                    ·
                      refine ⟨2821444231927900526442643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3761925642570534035256857 2821444231927900526442643)
                      ·
                        rfl

theorem cell23_5494743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_5494743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494743 prefixEnd_5494743 := by exact prefixLift 5494743
  have htrace : WordTrace (prefixWord ++ tailWord_5494743) baseStart_5494743 baseEnd_5494743 := by
    simpa [prefixWord, tailWord_5494743, baseEnd_5494743] using wordTrace_append hprefix tailTrace_5494743
  have hstable : (prefixWord ++ tailWord_5494743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494743).length < 2 ^ (prefixWord ++ tailWord_5494743).sum := by decide
  have hdescent : baseEnd_5494743 < baseStart_5494743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494779 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 7]
def baseStart_5494779 : Nat := 118140960795 + 5494779 * 2 ^ 59
def prefixEnd_5494779 : Nat := 4983230072969 + 3 ^ 40 * 5494779 * 2
def baseEnd_5494779 : Nat := 313495857470162487288053

theorem tailTrace_5494779 : CollatzResearch.WordTrace tailWord_5494779 prefixEnd_5494779 313495857470162487288053 := by
  unfold tailWord_5494779
  simp only [CollatzResearch.WordTrace]
  refine ⟨200411054560361591385799391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133607369706907727590532927 200411054560361591385799391)
  ·
    refine ⟨300616581840542387078699087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200411054560361591385799391 300616581840542387078699087)
    ·
      refine ⟨450924872760813580618048631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300616581840542387078699087 450924872760813580618048631)
      ·
        refine ⟨676387309141220370927072947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450924872760813580618048631 676387309141220370927072947)
        ·
          refine ⟨1014580963711830556390609421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676387309141220370927072947 1014580963711830556390609421)
          ·
            refine ⟨380467861391936458646478533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1014580963711830556390609421 380467861391936458646478533)
            ·
              refine ⟨71337724010988085996214725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 380467861391936458646478533 71337724010988085996214725)
              ·
                refine ⟨13375823252060266124290261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71337724010988085996214725 13375823252060266124290261)
                ·
                  refine ⟨313495857470162487288053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13375823252060266124290261 313495857470162487288053)
                  ·
                    rfl

theorem cell23_5494779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 7].length) (baseStart_5494779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494779 prefixEnd_5494779 := by exact prefixLift 5494779
  have htrace : WordTrace (prefixWord ++ tailWord_5494779) baseStart_5494779 baseEnd_5494779 := by
    simpa [prefixWord, tailWord_5494779, baseEnd_5494779] using wordTrace_append hprefix tailTrace_5494779
  have hstable : (prefixWord ++ tailWord_5494779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494779).length < 2 ^ (prefixWord ++ tailWord_5494779).sum := by decide
  have hdescent : baseEnd_5494779 < baseStart_5494779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494809 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_5494809 : Nat := 118140960795 + 5494809 * 2 ^ 59
def prefixEnd_5494809 : Nat := 4983230072969 + 3 ^ 40 * 5494809 * 2
def baseEnd_5494809 : Nat := 940492707217032422739113

theorem tailTrace_5494809 : CollatzResearch.WordTrace tailWord_5494809 prefixEnd_5494809 940492707217032422739113 := by
  unfold tailWord_5494809
  simp only [CollatzResearch.WordTrace]
  refine ⟨200412148750252906509391481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133608099166835271006260987 200412148750252906509391481)
  ·
    refine ⟨150309111562689679882043611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200412148750252906509391481 150309111562689679882043611)
    ·
      refine ⟨225463667344034519823065417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150309111562689679882043611 225463667344034519823065417)
      ·
        refine ⟨169097750508025889867299063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225463667344034519823065417 169097750508025889867299063)
        ·
          refine ⟨253646625762038834800948595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169097750508025889867299063 253646625762038834800948595)
          ·
            refine ⟨380469938643058252201422893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253646625762038834800948595 380469938643058252201422893)
            ·
              refine ⟨142676226991146844575533585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380469938643058252201422893 142676226991146844575533585)
              ·
                refine ⟨107007170243360133431650189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142676226991146844575533585 107007170243360133431650189)
                ·
                  refine ⟨40127688841260050036868821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107007170243360133431650189 40127688841260050036868821)
                  ·
                    refine ⟨940492707217032422739113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40127688841260050036868821 940492707217032422739113)
                    ·
                      rfl

theorem cell23_5494809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_5494809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494809 prefixEnd_5494809 := by exact prefixLift 5494809
  have htrace : WordTrace (prefixWord ++ tailWord_5494809) baseStart_5494809 baseEnd_5494809 := by
    simpa [prefixWord, tailWord_5494809, baseEnd_5494809] using wordTrace_append hprefix tailTrace_5494809
  have hstable : (prefixWord ++ tailWord_5494809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494809).length < 2 ^ (prefixWord ++ tailWord_5494809).sum := by decide
  have hdescent : baseEnd_5494809 < baseStart_5494809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494873 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 3, 4]
def baseStart_5494873 : Nat := 118140960795 + 5494873 * 2 ^ 59
def prefixEnd_5494873 : Nat := 4983230072969 + 3 ^ 40 * 5494873 * 2
def baseEnd_5494873 : Nat := 940503661470995005939015

theorem tailTrace_5494873 : CollatzResearch.WordTrace tailWord_5494873 prefixEnd_5494873 940503661470995005939015 := by
  unfold tailWord_5494873
  simp only [CollatzResearch.WordTrace]
  refine ⟨200414483022021045439721273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133609655348014030293147515 200414483022021045439721273)
  ·
    refine ⟨150310862266515784079790955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200414483022021045439721273 150310862266515784079790955)
    ·
      refine ⟨225466293399773676119686433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150310862266515784079790955 225466293399773676119686433)
      ·
        refine ⟨169099720049830257089764825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225466293399773676119686433 169099720049830257089764825)
        ·
          refine ⟨126824790037372692817323619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169099720049830257089764825 126824790037372692817323619)
          ·
            refine ⟨190237185056059039225985429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126824790037372692817323619 190237185056059039225985429)
            ·
              refine ⟨8917368049502767463718067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190237185056059039225985429 8917368049502767463718067)
              ·
                refine ⟨13376052074254151195577101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8917368049502767463718067 13376052074254151195577101)
                ·
                  refine ⟨5016019527845306698341413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13376052074254151195577101 5016019527845306698341413)
                  ·
                    refine ⟨940503661470995005939015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016019527845306698341413 940503661470995005939015)
                    ·
                      rfl

theorem cell23_5494873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_5494873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494873 prefixEnd_5494873 := by exact prefixLift 5494873
  have htrace : WordTrace (prefixWord ++ tailWord_5494873) baseStart_5494873 baseEnd_5494873 := by
    simpa [prefixWord, tailWord_5494873, baseEnd_5494873] using wordTrace_append hprefix tailTrace_5494873
  have hstable : (prefixWord ++ tailWord_5494873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494873).length < 2 ^ (prefixWord ++ tailWord_5494873).sum := by decide
  have hdescent : baseEnd_5494873 < baseStart_5494873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494940 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_5494940 : Nat := 118140960795 + 5494940 * 2 ^ 59
def prefixEnd_5494940 : Nat := 4983230072969 + 3 ^ 40 * 5494940 * 2
def baseEnd_5494940 : Nat := 2821545387616836255679237

theorem tailTrace_5494940 : CollatzResearch.WordTrace tailWord_5494940 prefixEnd_5494940 2821545387616836255679237 := by
  unfold tailWord_5494940
  simp only [CollatzResearch.WordTrace]
  refine ⟨100208463356389157941205137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133611284475185543921606849 100208463356389157941205137)
  ·
    refine ⟨75156347517291868455903853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100208463356389157941205137 75156347517291868455903853)
    ·
      refine ⟨28183630318984450670963945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75156347517291868455903853 28183630318984450670963945)
      ·
        refine ⟨21137722739238338003222959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28183630318984450670963945 21137722739238338003222959)
        ·
          refine ⟨31706584108857507004834439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21137722739238338003222959 31706584108857507004834439)
          ·
            refine ⟨47559876163286260507251659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31706584108857507004834439 47559876163286260507251659)
            ·
              refine ⟨71339814244929390760877489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47559876163286260507251659 71339814244929390760877489)
              ·
                refine ⟨53504860683697043070658117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71339814244929390760877489 53504860683697043070658117)
                ·
                  refine ⟨10032161378193195575748397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53504860683697043070658117 10032161378193195575748397)
                  ·
                    refine ⟨3762060516822448340905649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10032161378193195575748397 3762060516822448340905649)
                    ·
                      refine ⟨2821545387616836255679237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762060516822448340905649 2821545387616836255679237)
                      ·
                        rfl

theorem cell23_5494940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_5494940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494940 prefixEnd_5494940 := by exact prefixLift 5494940
  have htrace : WordTrace (prefixWord ++ tailWord_5494940) baseStart_5494940 baseEnd_5494940 := by
    simpa [prefixWord, tailWord_5494940, baseEnd_5494940] using wordTrace_append hprefix tailTrace_5494940
  have hstable : (prefixWord ++ tailWord_5494940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494940).length < 2 ^ (prefixWord ++ tailWord_5494940).sum := by decide
  have hdescent : baseEnd_5494940 < baseStart_5494940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494957 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_5494957 : Nat := 118140960795 + 5494957 * 2 ^ 59
def prefixEnd_5494957 : Nat := 4983230072969 + 3 ^ 40 * 5494957 * 2
def baseEnd_5494957 : Nat := 2821554116787962689166659

theorem tailTrace_5494957 : CollatzResearch.WordTrace tailWord_5494957 prefixEnd_5494957 2821554116787962689166659 := by
  unfold tailWord_5494957
  simp only [CollatzResearch.WordTrace]
  refine ⟨200417546753716727785779125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133611697835811151857186083 200417546753716727785779125)
  ·
    refine ⟨18789145008160943229916793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200417546753716727785779125 18789145008160943229916793)
    ·
      refine ⟨14091858756120707422437595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18789145008160943229916793 14091858756120707422437595)
      ·
        refine ⟨21137788134181061133656393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14091858756120707422437595 21137788134181061133656393)
        ·
          refine ⟨15853341100635795850242295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21137788134181061133656393 15853341100635795850242295)
          ·
            refine ⟨23780011650953693775363443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15853341100635795850242295 23780011650953693775363443)
            ·
              refine ⟨35670017476430540663045165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23780011650953693775363443 35670017476430540663045165)
              ·
                refine ⟨13376256553661452748641937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35670017476430540663045165 13376256553661452748641937)
                ·
                  refine ⟨10032192415246089561481453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13376256553661452748641937 10032192415246089561481453)
                  ·
                    refine ⟨3762072155717283585555545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10032192415246089561481453 3762072155717283585555545)
                    ·
                      refine ⟨2821554116787962689166659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762072155717283585555545 2821554116787962689166659)
                      ·
                        rfl

theorem cell23_5494957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_5494957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494957 prefixEnd_5494957 := by exact prefixLift 5494957
  have htrace : WordTrace (prefixWord ++ tailWord_5494957) baseStart_5494957 baseEnd_5494957 := by
    simpa [prefixWord, tailWord_5494957, baseEnd_5494957] using wordTrace_append hprefix tailTrace_5494957
  have hstable : (prefixWord ++ tailWord_5494957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494957).length < 2 ^ (prefixWord ++ tailWord_5494957).sum := by decide
  have hdescent : baseEnd_5494957 < baseStart_5494957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494976 : List Nat := [2, 1, 1, 2, 5, 12]
def baseStart_5494976 : Nat := 118140960795 + 5494976 * 2 ^ 59
def prefixEnd_5494976 : Nat := 4983230072969 + 3 ^ 40 * 5494976 * 2
def baseEnd_5494976 : Nat := 11611373962635383188597

theorem tailTrace_5494976 : CollatzResearch.WordTrace tailWord_5494976 prefixEnd_5494976 11611373962635383188597 := by
  unfold tailWord_5494976
  simp only [CollatzResearch.WordTrace]
  refine ⟨100209119870323947015360391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133612159827098596020480521 100209119870323947015360391)
  ·
    refine ⟨150313679805485920523040587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100209119870323947015360391 150313679805485920523040587)
    ·
      refine ⟨225470519708228880784560881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150313679805485920523040587 225470519708228880784560881)
      ·
        refine ⟨169102889781171660588420661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225470519708228880784560881 169102889781171660588420661)
        ·
          refine ⟨15853395916984843180164437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169102889781171660588420661 15853395916984843180164437)
          ·
            refine ⟨11611373962635383188597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15853395916984843180164437 11611373962635383188597)
            ·
              rfl

theorem cell23_5494976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 12].length) (baseStart_5494976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494976 prefixEnd_5494976 := by exact prefixLift 5494976
  have htrace : WordTrace (prefixWord ++ tailWord_5494976) baseStart_5494976 baseEnd_5494976 := by
    simpa [prefixWord, tailWord_5494976, baseEnd_5494976] using wordTrace_append hprefix tailTrace_5494976
  have hstable : (prefixWord ++ tailWord_5494976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494976).length < 2 ^ (prefixWord ++ tailWord_5494976).sum := by decide
  have hdescent : baseEnd_5494976 < baseStart_5494976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5494990 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_5494990 : Nat := 118140960795 + 5494990 * 2 ^ 59
def prefixEnd_5494990 : Nat := 4983230072969 + 3 ^ 40 * 5494990 * 2
def baseEnd_5494990 : Nat := 2821571061649561060054007

theorem tailTrace_5494990 : CollatzResearch.WordTrace tailWord_5494990 prefixEnd_5494990 2821571061649561060054007 := by
  unfold tailWord_5494990
  simp only [CollatzResearch.WordTrace]
  refine ⟨25052343795324646802716303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133612500241731449614486949 25052343795324646802716303)
  ·
    refine ⟨37578515692986970204074455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25052343795324646802716303 37578515692986970204074455)
    ·
      refine ⟨56367773539480455306111683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37578515692986970204074455 56367773539480455306111683)
      ·
        refine ⟨84551660309220682959167525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56367773539480455306111683 84551660309220682959167525)
        ·
          refine ⟨15853436307978878054843911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84551660309220682959167525 15853436307978878054843911)
          ·
            refine ⟨23780154461968317082265867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15853436307978878054843911 23780154461968317082265867)
            ·
              refine ⟨35670231692952475623398801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23780154461968317082265867 35670231692952475623398801)
              ·
                refine ⟨26752673769714356717549101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35670231692952475623398801 26752673769714356717549101)
                ·
                  refine ⟨10032252663642883769080913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26752673769714356717549101 10032252663642883769080913)
                  ·
                    refine ⟨7524189497732162826810685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10032252663642883769080913 7524189497732162826810685)
                    ·
                      refine ⟨2821571061649561060054007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7524189497732162826810685 2821571061649561060054007)
                      ·
                        rfl

theorem cell23_5494990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_5494990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5494990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5494990 prefixEnd_5494990 := by exact prefixLift 5494990
  have htrace : WordTrace (prefixWord ++ tailWord_5494990) baseStart_5494990 baseEnd_5494990 := by
    simpa [prefixWord, tailWord_5494990, baseEnd_5494990] using wordTrace_append hprefix tailTrace_5494990
  have hstable : (prefixWord ++ tailWord_5494990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5494990).length < 2 ^ (prefixWord ++ tailWord_5494990).sum := by decide
  have hdescent : baseEnd_5494990 < baseStart_5494990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5494990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495000 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_5495000 : Nat := 118140960795 + 5495000 * 2 ^ 59
def prefixEnd_5495000 : Nat := 4983230072969 + 3 ^ 40 * 5495000 * 2
def baseEnd_5495000 : Nat := 2821576196456106020928961

theorem tailTrace_5495000 : CollatzResearch.WordTrace tailWord_5495000 prefixEnd_5495000 2821576196456106020928961 := by
  unfold tailWord_5495000
  simp only [CollatzResearch.WordTrace]
  refine ⟨100209557546280473064797227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133612743395040630753062969 100209557546280473064797227)
  ·
    refine ⟨150314336319420709597195841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100209557546280473064797227 150314336319420709597195841)
    ·
      refine ⟨112735752239565532197896881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150314336319420709597195841 112735752239565532197896881)
      ·
        refine ⟨84551814179674149148422661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112735752239565532197896881 84551814179674149148422661)
        ·
          refine ⟨15853465158688902965329249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84551814179674149148422661 15853465158688902965329249)
          ·
            refine ⟨11890098869016677223996937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15853465158688902965329249 11890098869016677223996937)
            ·
              refine ⟨8917574151762507917997703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11890098869016677223996937 8917574151762507917997703)
              ·
                refine ⟨13376361227643761876996555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8917574151762507917997703 13376361227643761876996555)
                ·
                  refine ⟨20064541841465642815494833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13376361227643761876996555 20064541841465642815494833)
                  ·
                    refine ⟨15048406381099232111621125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20064541841465642815494833 15048406381099232111621125)
                    ·
                      refine ⟨2821576196456106020928961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15048406381099232111621125 2821576196456106020928961)
                      ·
                        rfl

theorem cell23_5495000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_5495000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495000 prefixEnd_5495000 := by exact prefixLift 5495000
  have htrace : WordTrace (prefixWord ++ tailWord_5495000) baseStart_5495000 baseEnd_5495000 := by
    simpa [prefixWord, tailWord_5495000, baseEnd_5495000] using wordTrace_append hprefix tailTrace_5495000
  have hstable : (prefixWord ++ tailWord_5495000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495000).length < 2 ^ (prefixWord ++ tailWord_5495000).sum := by decide
  have hdescent : baseEnd_5495000 < baseStart_5495000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495003 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 3]
def baseStart_5495003 : Nat := 118140960795 + 5495003 * 2 ^ 59
def prefixEnd_5495003 : Nat := 4983230072969 + 3 ^ 40 * 5495003 * 2
def baseEnd_5495003 : Nat := 2821577736898069509191447

theorem tailTrace_5495003 : CollatzResearch.WordTrace tailWord_5495003 prefixEnd_5495003 2821577736898069509191447 := by
  unfold tailWord_5495003
  simp only [CollatzResearch.WordTrace]
  refine ⟨200419224511550077641953663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133612816341033385094635775 200419224511550077641953663)
  ·
    refine ⟨300628836767325116462930495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200419224511550077641953663 300628836767325116462930495)
    ·
      refine ⟨450943255150987674694395743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300628836767325116462930495 450943255150987674694395743)
      ·
        refine ⟨676414882726481512041593615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450943255150987674694395743 676414882726481512041593615)
        ·
          refine ⟨1014622324089722268062390423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676414882726481512041593615 1014622324089722268062390423)
          ·
            refine ⟨1521933486134583402093585635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014622324089722268062390423 1521933486134583402093585635)
            ·
              refine ⟨2282900229201875103140378453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521933486134583402093585635 2282900229201875103140378453)
              ·
                refine ⟨13376368530479736932463155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2282900229201875103140378453 13376368530479736932463155)
                ·
                  refine ⟨20064552795719605398694733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13376368530479736932463155 20064552795719605398694733)
                  ·
                    refine ⟨7524207298394852024510525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20064552795719605398694733 7524207298394852024510525)
                    ·
                      refine ⟨2821577736898069509191447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7524207298394852024510525 2821577736898069509191447)
                      ·
                        rfl

theorem cell23_5495003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 3].length) (baseStart_5495003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495003 prefixEnd_5495003 := by exact prefixLift 5495003
  have htrace : WordTrace (prefixWord ++ tailWord_5495003) baseStart_5495003 baseEnd_5495003 := by
    simpa [prefixWord, tailWord_5495003, baseEnd_5495003] using wordTrace_append hprefix tailTrace_5495003
  have hstable : (prefixWord ++ tailWord_5495003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495003).length < 2 ^ (prefixWord ++ tailWord_5495003).sum := by decide
  have hdescent : baseEnd_5495003 < baseStart_5495003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495020 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_5495020 : Nat := 118140960795 + 5495020 * 2 ^ 59
def prefixEnd_5495020 : Nat := 4983230072969 + 3 ^ 40 * 5495020 * 2
def baseEnd_5495020 : Nat := 2821586466069195942678869

theorem tailTrace_5495020 : CollatzResearch.WordTrace tailWord_5495020 prefixEnd_5495020 2821586466069195942678869 := by
  unfold tailWord_5495020
  simp only [CollatzResearch.WordTrace]
  refine ⟨100209922276244244772661257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133613229701658993030215009 100209922276244244772661257)
  ·
    refine ⟨75157441707183183579495943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100209922276244244772661257 75157441707183183579495943)
    ·
      refine ⟨112736162560774775369243915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75157441707183183579495943 112736162560774775369243915)
      ·
        refine ⟨169104243841162163053865873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112736162560774775369243915 169104243841162163053865873)
        ·
          refine ⟨126828182880871622290399405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169104243841162163053865873 126828182880871622290399405)
          ·
            refine ⟨47560568580326858358899777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126828182880871622290399405 47560568580326858358899777)
            ·
              refine ⟨35670426435245143769174833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47560568580326858358899777 35670426435245143769174833)
              ·
                refine ⟨26752819826433857826881125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35670426435245143769174833 26752819826433857826881125)
                ·
                  refine ⟨5016153717456348342540211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26752819826433857826881125 5016153717456348342540211)
                  ·
                    refine ⟨7524230576184522513810317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5016153717456348342540211 7524230576184522513810317)
                    ·
                      refine ⟨2821586466069195942678869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7524230576184522513810317 2821586466069195942678869)
                      ·
                        rfl

theorem cell23_5495020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_5495020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495020 prefixEnd_5495020 := by exact prefixLift 5495020
  have htrace : WordTrace (prefixWord ++ tailWord_5495020) baseStart_5495020 baseEnd_5495020 := by
    simpa [prefixWord, tailWord_5495020, baseEnd_5495020] using wordTrace_append hprefix tailTrace_5495020
  have hstable : (prefixWord ++ tailWord_5495020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495020).length < 2 ^ (prefixWord ++ tailWord_5495020).sum := by decide
  have hdescent : baseEnd_5495020 < baseStart_5495020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495021 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5495021 : Nat := 118140960795 + 5495021 * 2 ^ 59
def prefixEnd_5495021 : Nat := 4983230072969 + 3 ^ 40 * 5495021 * 2
def baseEnd_5495021 : Nat := 2821586979549850438766365

theorem tailTrace_5495021 : CollatzResearch.WordTrace tailWord_5495021 prefixEnd_5495021 2821586979549850438766365 := by
  unfold tailWord_5495021
  simp only [CollatzResearch.WordTrace]
  refine ⟨200419881025484866716108917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133613254016989911144072611 200419881025484866716108917)
  ·
    refine ⟨18789363846139206254635211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200419881025484866716108917 18789363846139206254635211)
    ·
      refine ⟨28184045769208809381952817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18789363846139206254635211 28184045769208809381952817)
      ·
        refine ⟨21138034326906607036464613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28184045769208809381952817 21138034326906607036464613)
        ·
          refine ⟨3963381436294988819337115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21138034326906607036464613 3963381436294988819337115)
          ·
            refine ⟨5945072154442483229005673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963381436294988819337115 5945072154442483229005673)
            ·
              refine ⟨4458804115831862421754255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5945072154442483229005673 4458804115831862421754255)
              ·
                refine ⟨6688206173747793632631383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458804115831862421754255 6688206173747793632631383)
                ·
                  refine ⟨10032309260621690448947075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6688206173747793632631383 10032309260621690448947075)
                  ·
                    refine ⟨15048463890932535673420613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10032309260621690448947075 15048463890932535673420613)
                    ·
                      refine ⟨2821586979549850438766365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15048463890932535673420613 2821586979549850438766365)
                      ·
                        rfl

theorem cell23_5495021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5495021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495021 prefixEnd_5495021 := by exact prefixLift 5495021
  have htrace : WordTrace (prefixWord ++ tailWord_5495021) baseStart_5495021 baseEnd_5495021 := by
    simpa [prefixWord, tailWord_5495021, baseEnd_5495021] using wordTrace_append hprefix tailTrace_5495021
  have hstable : (prefixWord ++ tailWord_5495021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495021).length < 2 ^ (prefixWord ++ tailWord_5495021).sum := by decide
  have hdescent : baseEnd_5495021 < baseStart_5495021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495054 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_5495054 : Nat := 118140960795 + 5495054 * 2 ^ 59
def prefixEnd_5495054 : Nat := 4983230072969 + 3 ^ 40 * 5495054 * 2
def baseEnd_5495054 : Nat := 2821603924411448809653713

theorem tailTrace_5495054 : CollatzResearch.WordTrace tailWord_5495054 prefixEnd_5495054 2821603924411448809653713 := by
  unfold tailWord_5495054
  simp only [CollatzResearch.WordTrace]
  refine ⟨25052635579295664169007527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133614056422910208901373477 25052635579295664169007527)
  ·
    refine ⟨37578953368943496253511291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25052635579295664169007527 37578953368943496253511291)
    ·
      refine ⟨56368430053415244380266937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37578953368943496253511291 56368430053415244380266937)
      ·
        refine ⟨42276322540061433285200203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56368430053415244380266937 42276322540061433285200203)
        ·
          refine ⟨63414483810092149927800305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42276322540061433285200203 63414483810092149927800305)
          ·
            refine ⟨47560862857569112445850229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63414483810092149927800305 47560862857569112445850229)
            ·
              refine ⟨4458830892897104291798459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47560862857569112445850229 4458830892897104291798459)
              ·
                refine ⟨6688246339345656437697689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458830892897104291798459 6688246339345656437697689)
                ·
                  refine ⟨5016184754509242328273267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6688246339345656437697689 5016184754509242328273267)
                  ·
                    refine ⟨7524277131763863492409901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5016184754509242328273267 7524277131763863492409901)
                    ·
                      refine ⟨2821603924411448809653713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7524277131763863492409901 2821603924411448809653713)
                      ·
                        rfl

theorem cell23_5495054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_5495054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495054 prefixEnd_5495054 := by exact prefixLift 5495054
  have htrace : WordTrace (prefixWord ++ tailWord_5495054) baseStart_5495054 baseEnd_5495054 := by
    simpa [prefixWord, tailWord_5495054, baseEnd_5495054] using wordTrace_append hprefix tailTrace_5495054
  have hstable : (prefixWord ++ tailWord_5495054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495054).length < 2 ^ (prefixWord ++ tailWord_5495054).sum := by decide
  have hdescent : baseEnd_5495054 < baseStart_5495054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495073 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_5495073 : Nat := 118140960795 + 5495073 * 2 ^ 59
def prefixEnd_5495073 : Nat := 4983230072969 + 3 ^ 40 * 5495073 * 2
def baseEnd_5495073 : Nat := 2821613680543884235316125

theorem tailTrace_5495073 : CollatzResearch.WordTrace tailWord_5495073 prefixEnd_5495073 2821613680543884235316125 := by
  unfold tailWord_5495073
  simp only [CollatzResearch.WordTrace]
  refine ⟨200421777621296479597001873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133614518414197653064667915 200421777621296479597001873)
  ·
    refine ⟨150316333215972359697751405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200421777621296479597001873 150316333215972359697751405)
    ·
      refine ⟨56368624955989634886656777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150316333215972359697751405 56368624955989634886656777)
      ·
        refine ⟨42276468716992226164992583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56368624955989634886656777 42276468716992226164992583)
        ·
          refine ⟨63414703075488339247488875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42276468716992226164992583 63414703075488339247488875)
          ·
            refine ⟨95122054613232508871233313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63414703075488339247488875 95122054613232508871233313)
            ·
              refine ⟨71341540959924381653424985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95122054613232508871233313 71341540959924381653424985)
              ·
                refine ⟨53506155719943286240068739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71341540959924381653424985 53506155719943286240068739)
                ·
                  refine ⟨80259233579914929360103109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53506155719943286240068739 80259233579914929360103109)
                  ·
                    refine ⟨15048606296234049255019333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80259233579914929360103109 15048606296234049255019333)
                    ·
                      refine ⟨2821613680543884235316125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15048606296234049255019333 2821613680543884235316125)
                      ·
                        rfl

theorem cell23_5495073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_5495073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495073 prefixEnd_5495073 := by exact prefixLift 5495073
  have htrace : WordTrace (prefixWord ++ tailWord_5495073) baseStart_5495073 baseEnd_5495073 := by
    simpa [prefixWord, tailWord_5495073, baseEnd_5495073] using wordTrace_append hprefix tailTrace_5495073
  have hstable : (prefixWord ++ tailWord_5495073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495073).length < 2 ^ (prefixWord ++ tailWord_5495073).sum := by decide
  have hdescent : baseEnd_5495073 < baseStart_5495073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495093 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5495093 : Nat := 118140960795 + 5495093 * 2 ^ 59
def prefixEnd_5495093 : Nat := 4983230072969 + 3 ^ 40 * 5495093 * 2
def baseEnd_5495093 : Nat := 2821623950156974157066033

theorem tailTrace_5495093 : CollatzResearch.WordTrace tailWord_5495093 prefixEnd_5495093 2821623950156974157066033 := by
  unfold tailWord_5495093
  simp only [CollatzResearch.WordTrace]
  refine ⟨200422507081224023012729933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133615004720816015341819955 200422507081224023012729933)
  ·
    refine ⟨75158440155459008629773725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200422507081224023012729933 75158440155459008629773725)
    ·
      refine ⟨28184415058297128236165147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75158440155459008629773725 28184415058297128236165147)
      ·
        refine ⟨42276622587445692354247721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28184415058297128236165147 42276622587445692354247721)
        ·
          refine ⟨31707466940584269265685791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42276622587445692354247721 31707466940584269265685791)
          ·
            refine ⟨47561200410876403898528687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31707466940584269265685791 47561200410876403898528687)
            ·
              refine ⟨71341800616314605847793031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47561200410876403898528687 71341800616314605847793031)
              ·
                refine ⟨107012700924471908771689547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71341800616314605847793031 107012700924471908771689547)
                ·
                  refine ⟨160519051386707863157534321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107012700924471908771689547 160519051386707863157534321)
                  ·
                    refine ⟨120389288540030897368150741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160519051386707863157534321 120389288540030897368150741)
                    ·
                      refine ⟨2821623950156974157066033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120389288540030897368150741 2821623950156974157066033)
                      ·
                        rfl

theorem cell23_5495093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5495093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495093 prefixEnd_5495093 := by exact prefixLift 5495093
  have htrace : WordTrace (prefixWord ++ tailWord_5495093) baseStart_5495093 baseEnd_5495093 := by
    simpa [prefixWord, tailWord_5495093, baseEnd_5495093] using wordTrace_append hprefix tailTrace_5495093
  have hstable : (prefixWord ++ tailWord_5495093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495093).length < 2 ^ (prefixWord ++ tailWord_5495093).sum := by decide
  have hdescent : baseEnd_5495093 < baseStart_5495093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495113 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_5495113 : Nat := 118140960795 + 5495113 * 2 ^ 59
def prefixEnd_5495113 : Nat := 4983230072969 + 3 ^ 40 * 5495113 * 2
def baseEnd_5495113 : Nat := 940544739923354692938647

theorem tailTrace_5495113 : CollatzResearch.WordTrace tailWord_5495113 prefixEnd_5495113 940544739923354692938647 := by
  unfold tailWord_5495113
  simp only [CollatzResearch.WordTrace]
  refine ⟨200423236541151566428457993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133615491027434377618971995 200423236541151566428457993)
  ·
    refine ⟨150317427405863674821343495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200423236541151566428457993 150317427405863674821343495)
    ·
      refine ⟨225476141108795512232015243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150317427405863674821343495 225476141108795512232015243)
      ·
        refine ⟨338214211663193268348022865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225476141108795512232015243 338214211663193268348022865)
        ·
          refine ⟨253660658747394951261017149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338214211663193268348022865 253660658747394951261017149)
          ·
            refine ⟨95122747030273106722881431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253660658747394951261017149 95122747030273106722881431)
            ·
              refine ⟨142684120545409660084322147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95122747030273106722881431 142684120545409660084322147)
              ·
                refine ⟨214026180818114490126483221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142684120545409660084322147 214026180818114490126483221)
                ·
                  refine ⟨10032477225849116724678901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214026180818114490126483221 10032477225849116724678901)
                  ·
                    refine ⟨940544739923354692938647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10032477225849116724678901 940544739923354692938647)
                    ·
                      rfl

theorem cell23_5495113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_5495113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495113 prefixEnd_5495113 := by exact prefixLift 5495113
  have htrace : WordTrace (prefixWord ++ tailWord_5495113) baseStart_5495113 baseEnd_5495113 := by
    simpa [prefixWord, tailWord_5495113, baseEnd_5495113] using wordTrace_append hprefix tailTrace_5495113
  have hstable : (prefixWord ++ tailWord_5495113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495113).length < 2 ^ (prefixWord ++ tailWord_5495113).sum := by decide
  have hdescent : baseEnd_5495113 < baseStart_5495113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495153 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_5495153 : Nat := 118140960795 + 5495153 * 2 ^ 59
def prefixEnd_5495153 : Nat := 4983230072969 + 3 ^ 40 * 5495153 * 2
def baseEnd_5495153 : Nat := 2821654758996243922315757

theorem tailTrace_5495153 : CollatzResearch.WordTrace tailWord_5495153 prefixEnd_5495153 2821654758996243922315757 := by
  unfold tailWord_5495153
  simp only [CollatzResearch.WordTrace]
  refine ⟨200424695461006653259914113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133616463640671102173276075 200424695461006653259914113)
  ·
    refine ⟨150318521595754989944935585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200424695461006653259914113 150318521595754989944935585)
    ·
      refine ⟨112738891196816242458701689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150318521595754989944935585 112738891196816242458701689)
      ·
        refine ⟨84554168397612181844026267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112738891196816242458701689 84554168397612181844026267)
        ·
          refine ⟨126831252596418272766039401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84554168397612181844026267 126831252596418272766039401)
          ·
            refine ⟨95123439447313704574529551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126831252596418272766039401 95123439447313704574529551)
            ·
              refine ⟨142685159170970556861794327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95123439447313704574529551 142685159170970556861794327)
              ·
                refine ⟨214027738756455835292691491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142685159170970556861794327 214027738756455835292691491)
                ·
                  refine ⟨321041608134683752939037237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214027738756455835292691491 321041608134683752939037237)
                  ·
                    refine ⟨30097650762626601838034741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 321041608134683752939037237 30097650762626601838034741)
                    ·
                      refine ⟨2821654758996243922315757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30097650762626601838034741 2821654758996243922315757)
                      ·
                        rfl

theorem cell23_5495153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_5495153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495153 prefixEnd_5495153 := by exact prefixLift 5495153
  have htrace : WordTrace (prefixWord ++ tailWord_5495153) baseStart_5495153 baseEnd_5495153 := by
    simpa [prefixWord, tailWord_5495153, baseEnd_5495153] using wordTrace_append hprefix tailTrace_5495153
  have hstable : (prefixWord ++ tailWord_5495153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495153).length < 2 ^ (prefixWord ++ tailWord_5495153).sum := by decide
  have hdescent : baseEnd_5495153 < baseStart_5495153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495173 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 10]
def baseStart_5495173 : Nat := 118140960795 + 5495173 * 2 ^ 59
def prefixEnd_5495173 : Nat := 4983230072969 + 3 ^ 40 * 5495173 * 2
def baseEnd_5495173 : Nat := 313518336512148204896185

theorem tailTrace_5495173 : CollatzResearch.WordTrace tailWord_5495173 prefixEnd_5495173 313518336512148204896185 := by
  unfold tailWord_5495173
  simp only [CollatzResearch.WordTrace]
  refine ⟨200425424920934196675642173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133616949947289464450428115 200425424920934196675642173)
  ·
    refine ⟨75159534345350323753365815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200425424920934196675642173 75159534345350323753365815)
    ·
      refine ⟨112739301518025485630048723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75159534345350323753365815 112739301518025485630048723)
      ·
        refine ⟨169108952277038228445073085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112739301518025485630048723 169108952277038228445073085)
        ·
          refine ⟨63415857103889335666902407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169108952277038228445073085 63415857103889335666902407)
          ·
            refine ⟨95123785655834003500353611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63415857103889335666902407 95123785655834003500353611)
            ·
              refine ⟨142685678483751005250530417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95123785655834003500353611 142685678483751005250530417)
              ·
                refine ⟨107014258862813253937897813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142685678483751005250530417 107014258862813253937897813)
                ·
                  refine ⟨313518336512148204896185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107014258862813253937897813 313518336512148204896185)
                  ·
                    rfl

theorem cell23_5495173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_5495173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495173 prefixEnd_5495173 := by exact prefixLift 5495173
  have htrace : WordTrace (prefixWord ++ tailWord_5495173) baseStart_5495173 baseEnd_5495173 := by
    simpa [prefixWord, tailWord_5495173, baseEnd_5495173] using wordTrace_append hprefix tailTrace_5495173
  have hstable : (prefixWord ++ tailWord_5495173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495173).length < 2 ^ (prefixWord ++ tailWord_5495173).sum := by decide
  have hdescent : baseEnd_5495173 < baseStart_5495173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495177 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 3, 4]
def baseStart_5495177 : Nat := 118140960795 + 5495177 * 2 ^ 59
def prefixEnd_5495177 : Nat := 4983230072969 + 3 ^ 40 * 5495177 * 2
def baseEnd_5495177 : Nat := 940555694177317276138549

theorem tailTrace_5495177 : CollatzResearch.WordTrace tailWord_5495177 prefixEnd_5495177 940555694177317276138549 := by
  unfold tailWord_5495177
  simp only [CollatzResearch.WordTrace]
  refine ⟨200425570812919705358787785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133617047208613136905858523 200425570812919705358787785)
  ·
    refine ⟨150319178109689779019090839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200425570812919705358787785 150319178109689779019090839)
    ·
      refine ⟨225478767164534668528636259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150319178109689779019090839 225478767164534668528636259)
      ·
        refine ⟨338218150746802002792954389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225478767164534668528636259 338218150746802002792954389)
        ·
          refine ⟨15853975816256343880919737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 338218150746802002792954389 15853975816256343880919737)
          ·
            refine ⟨11890481862192257910689803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15853975816256343880919737 11890481862192257910689803)
            ·
              refine ⟨17835722793288386866034705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11890481862192257910689803 17835722793288386866034705)
              ·
                refine ⟨13376792094966290149526029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17835722793288386866034705 13376792094966290149526029)
                ·
                  refine ⟨5016297035612358806072261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13376792094966290149526029 5016297035612358806072261)
                  ·
                    refine ⟨940555694177317276138549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016297035612358806072261 940555694177317276138549)
                    ·
                      rfl

theorem cell23_5495177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_5495177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495177 prefixEnd_5495177 := by exact prefixLift 5495177
  have htrace : WordTrace (prefixWord ++ tailWord_5495177) baseStart_5495177 baseEnd_5495177 := by
    simpa [prefixWord, tailWord_5495177, baseEnd_5495177] using wordTrace_append hprefix tailTrace_5495177
  have hstable : (prefixWord ++ tailWord_5495177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495177).length < 2 ^ (prefixWord ++ tailWord_5495177).sum := by decide
  have hdescent : baseEnd_5495177 < baseStart_5495177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495194 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_5495194 : Nat := 118140960795 + 5495194 * 2 ^ 59
def prefixEnd_5495194 : Nat := 4983230072969 + 3 ^ 40 * 5495194 * 2
def baseEnd_5495194 : Nat := 940558603901026087301023

theorem tailTrace_5495194 : CollatzResearch.WordTrace tailWord_5495194 prefixEnd_5495194 940558603901026087301023 := by
  unfold tailWord_5495194
  simp only [CollatzResearch.WordTrace]
  refine ⟨50106547713464529315539159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133617460569238744841437757 50106547713464529315539159)
  ·
    refine ⟨75159821570196793973308739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50106547713464529315539159 75159821570196793973308739)
    ·
      refine ⟨112739732355295190959963109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75159821570196793973308739 112739732355295190959963109)
      ·
        refine ⟨21138699816617848304993083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112739732355295190959963109 21138699816617848304993083)
        ·
          refine ⟨31708049724926772457489625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21138699816617848304993083 31708049724926772457489625)
          ·
            refine ⟨23781037293695079343117219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31708049724926772457489625 23781037293695079343117219)
            ·
              refine ⟨35671555940542619014675829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23781037293695079343117219 35671555940542619014675829)
              ·
                refine ⟨3344208369425870532625859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35671555940542619014675829 3344208369425870532625859)
                ·
                  refine ⟨5016312554138805798938789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344208369425870532625859 5016312554138805798938789)
                  ·
                    refine ⟨940558603901026087301023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016312554138805798938789 940558603901026087301023)
                    ·
                      rfl

theorem cell23_5495194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_5495194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495194 prefixEnd_5495194 := by exact prefixLift 5495194
  have htrace : WordTrace (prefixWord ++ tailWord_5495194) baseStart_5495194 baseEnd_5495194 := by
    simpa [prefixWord, tailWord_5495194, baseEnd_5495194] using wordTrace_append hprefix tailTrace_5495194
  have hstable : (prefixWord ++ tailWord_5495194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495194).length < 2 ^ (prefixWord ++ tailWord_5495194).sum := by decide
  have hdescent : baseEnd_5495194 < baseStart_5495194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495207 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 6]
def baseStart_5495207 : Nat := 118140960795 + 5495207 * 2 ^ 59
def prefixEnd_5495207 : Nat := 4983230072969 + 3 ^ 40 * 5495207 * 2
def baseEnd_5495207 : Nat := 313520276327954079004501

theorem tailTrace_5495207 : CollatzResearch.WordTrace tailWord_5495207 prefixEnd_5495207 313520276327954079004501 := by
  unfold tailWord_5495207
  simp only [CollatzResearch.WordTrace]
  refine ⟨200426665002811020482379875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133617776668540680321586583 200426665002811020482379875)
  ·
    refine ⟨300639997504216530723569813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200426665002811020482379875 300639997504216530723569813)
    ·
      refine ⟨14092499883010149877667335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 300639997504216530723569813 14092499883010149877667335)
      ·
        refine ⟨21138749824515224816501003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14092499883010149877667335 21138749824515224816501003)
        ·
          refine ⟨31708124736772837224751505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21138749824515224816501003 31708124736772837224751505)
          ·
            refine ⟨23781093552579627918563629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31708124736772837224751505 23781093552579627918563629)
            ·
              refine ⟨8917910082217360469461361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23781093552579627918563629 8917910082217360469461361)
              ·
                refine ⟨6688432561663020352096021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8917910082217360469461361 6688432561663020352096021)
                ·
                  refine ⟨313520276327954079004501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6688432561663020352096021 313520276327954079004501)
                  ·
                    rfl

theorem cell23_5495207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 6].length) (baseStart_5495207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495207 prefixEnd_5495207 := by exact prefixLift 5495207
  have htrace : WordTrace (prefixWord ++ tailWord_5495207) baseStart_5495207 baseEnd_5495207 := by
    simpa [prefixWord, tailWord_5495207, baseEnd_5495207] using wordTrace_append hprefix tailTrace_5495207
  have hstable : (prefixWord ++ tailWord_5495207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495207).length < 2 ^ (prefixWord ++ tailWord_5495207).sum := by decide
  have hdescent : baseEnd_5495207 < baseStart_5495207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495230 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5495230 : Nat := 118140960795 + 5495230 * 2 ^ 59
def prefixEnd_5495230 : Nat := 4983230072969 + 3 ^ 40 * 5495230 * 2
def baseEnd_5495230 : Nat := 2821694297006640121052903

theorem tailTrace_5495230 : CollatzResearch.WordTrace tailWord_5495230 prefixEnd_5495230 2821694297006640121052903 := by
  unfold tailWord_5495230
  simp only [CollatzResearch.WordTrace]
  refine ⟨25053437985215961926308393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133618335921151796940311429 25053437985215961926308393)
  ·
    refine ⟨18790078488911971444731295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25053437985215961926308393 18790078488911971444731295)
    ·
      refine ⟨28185117733367957167096943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18790078488911971444731295 28185117733367957167096943)
      ·
        refine ⟨42277676600051935750645415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28185117733367957167096943 42277676600051935750645415)
        ·
          refine ⟨63416514900077903625968123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42277676600051935750645415 63416514900077903625968123)
          ·
            refine ⟨95124772350116855438952185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63416514900077903625968123 95124772350116855438952185)
            ·
              refine ⟨71343579262587641579214139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95124772350116855438952185 71343579262587641579214139)
              ·
                refine ⟨107015368893881462368821209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71343579262587641579214139 107015368893881462368821209)
                ·
                  refine ⟨80261526670411096776615907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107015368893881462368821209 80261526670411096776615907)
                  ·
                    refine ⟨120392290005616645164923861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80261526670411096776615907 120392290005616645164923861)
                    ·
                      refine ⟨2821694297006640121052903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120392290005616645164923861 2821694297006640121052903)
                      ·
                        rfl

theorem cell23_5495230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5495230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495230 prefixEnd_5495230 := by exact prefixLift 5495230
  have htrace : WordTrace (prefixWord ++ tailWord_5495230) baseStart_5495230 baseEnd_5495230 := by
    simpa [prefixWord, tailWord_5495230, baseEnd_5495230] using wordTrace_append hprefix tailTrace_5495230
  have hstable : (prefixWord ++ tailWord_5495230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495230).length < 2 ^ (prefixWord ++ tailWord_5495230).sum := by decide
  have hdescent : baseEnd_5495230 < baseStart_5495230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495254 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5495254 : Nat := 118140960795 + 5495254 * 2 ^ 59
def prefixEnd_5495254 : Nat := 4983230072969 + 3 ^ 40 * 5495254 * 2
def baseEnd_5495254 : Nat := 940568873514116009050931

theorem tailTrace_5495254 : CollatzResearch.WordTrace tailWord_5495254 prefixEnd_5495254 940568873514116009050931 := by
  unfold tailWord_5495254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12526773702102546719333801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133618919489093831672893877 12526773702102546719333801)
  ·
    refine ⟨9395080276576910039500351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12526773702102546719333801 9395080276576910039500351)
    ·
      refine ⟨14092620414865365059250527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395080276576910039500351 14092620414865365059250527)
      ·
        refine ⟨21138930622298047588875791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14092620414865365059250527 21138930622298047588875791)
        ·
          refine ⟨31708395933447071383313687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21138930622298047588875791 31708395933447071383313687)
          ·
            refine ⟨47562593900170607074970531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31708395933447071383313687 47562593900170607074970531)
            ·
              refine ⟨71343890850255910612455797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47562593900170607074970531 71343890850255910612455797)
              ·
                refine ⟨6688489767211491619917731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71343890850255910612455797 6688489767211491619917731)
                ·
                  refine ⟨10032734650817237429876597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6688489767211491619917731 10032734650817237429876597)
                  ·
                    refine ⟨940568873514116009050931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10032734650817237429876597 940568873514116009050931)
                    ·
                      rfl

theorem cell23_5495254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5495254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495254 prefixEnd_5495254 := by exact prefixLift 5495254
  have htrace : WordTrace (prefixWord ++ tailWord_5495254) baseStart_5495254 baseEnd_5495254 := by
    simpa [prefixWord, tailWord_5495254, baseEnd_5495254] using wordTrace_append hprefix tailTrace_5495254
  have hstable : (prefixWord ++ tailWord_5495254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495254).length < 2 ^ (prefixWord ++ tailWord_5495254).sum := by decide
  have hdescent : baseEnd_5495254 < baseStart_5495254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495257 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 4]
def baseStart_5495257 : Nat := 118140960795 + 5495257 * 2 ^ 59
def prefixEnd_5495257 : Nat := 4983230072969 + 3 ^ 40 * 5495257 * 2
def baseEnd_5495257 : Nat := 2821708160984311515415279

theorem tailTrace_5495257 : CollatzResearch.WordTrace tailWord_5495257 prefixEnd_5495257 2821708160984311515415279 := by
  unfold tailWord_5495257
  simp only [CollatzResearch.WordTrace]
  refine ⟨200428488652629879021700025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133618992435086586014466683 200428488652629879021700025)
  ·
    refine ⟨150321366489472409266275019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200428488652629879021700025 150321366489472409266275019)
    ·
      refine ⟨225482049734208613899412529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150321366489472409266275019 225482049734208613899412529)
      ·
        refine ⟨169111537300656460424559397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225482049734208613899412529 169111537300656460424559397)
        ·
          refine ⟨31708413243873086329604887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169111537300656460424559397 31708413243873086329604887)
          ·
            refine ⟨47562619865809629494407331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31708413243873086329604887 47562619865809629494407331)
            ·
              refine ⟨71343929798714444241610997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47562619865809629494407331 71343929798714444241610997)
              ·
                refine ⟨6688493418629479147651031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71343929798714444241610997 6688493418629479147651031)
                ·
                  refine ⟨10032740127944218721476547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6688493418629479147651031 10032740127944218721476547)
                  ·
                    refine ⟨15049110191916328082214821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10032740127944218721476547 15049110191916328082214821)
                    ·
                      refine ⟨2821708160984311515415279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15049110191916328082214821 2821708160984311515415279)
                      ·
                        rfl

theorem cell23_5495257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_5495257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495257 prefixEnd_5495257 := by exact prefixLift 5495257
  have htrace : WordTrace (prefixWord ++ tailWord_5495257) baseStart_5495257 baseEnd_5495257 := by
    simpa [prefixWord, tailWord_5495257, baseEnd_5495257] using wordTrace_append hprefix tailTrace_5495257
  have hstable : (prefixWord ++ tailWord_5495257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495257).length < 2 ^ (prefixWord ++ tailWord_5495257).sum := by decide
  have hdescent : baseEnd_5495257 < baseStart_5495257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495280 : List Nat := [2, 1, 1, 1, 3, 3, 4, 8]
def baseStart_5495280 : Nat := 118140960795 + 5495280 * 2 ^ 59
def prefixEnd_5495280 : Nat := 4983230072969 + 3 ^ 40 * 5495280 * 2
def baseEnd_5495280 : Nat := 104508147075532034275099

theorem tailTrace_5495280 : CollatzResearch.WordTrace tailWord_5495280 prefixEnd_5495280 104508147075532034275099 := by
  unfold tailWord_5495280
  simp only [CollatzResearch.WordTrace]
  refine ⟨100214663765773276974893647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133619551687697702633191529 100214663765773276974893647)
  ·
    refine ⟨150321995648659915462340471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100214663765773276974893647 150321995648659915462340471)
    ·
      refine ⟨225482993472989873193510707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150321995648659915462340471 225482993472989873193510707)
      ·
        refine ⟨338224490209484809790266061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225482993472989873193510707 338224490209484809790266061)
        ·
          refine ⟨126834183828556803671349773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338224490209484809790266061 126834183828556803671349773)
          ·
            refine ⟨47562818935708801376756165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126834183828556803671349773 47562818935708801376756165)
            ·
              refine ⟨8918028550445400258141781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47562818935708801376756165 8918028550445400258141781)
              ·
                refine ⟨104508147075532034275099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8918028550445400258141781 104508147075532034275099)
                ·
                  rfl

theorem cell23_5495280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 8].length) (baseStart_5495280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495280 prefixEnd_5495280 := by exact prefixLift 5495280
  have htrace : WordTrace (prefixWord ++ tailWord_5495280) baseStart_5495280 baseEnd_5495280 := by
    simpa [prefixWord, tailWord_5495280, baseEnd_5495280] using wordTrace_append hprefix tailTrace_5495280
  have hstable : (prefixWord ++ tailWord_5495280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495280).length < 2 ^ (prefixWord ++ tailWord_5495280).sum := by decide
  have hdescent : baseEnd_5495280 < baseStart_5495280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495307 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 3]
def baseStart_5495307 : Nat := 118140960795 + 5495307 * 2 ^ 59
def prefixEnd_5495307 : Nat := 4983230072969 + 3 ^ 40 * 5495307 * 2
def baseEnd_5495307 : Nat := 2821733835017036319790049

theorem tailTrace_5495307 : CollatzResearch.WordTrace tailWord_5495307 prefixEnd_5495307 2821733835017036319790049 := by
  unfold tailWord_5495307
  simp only [CollatzResearch.WordTrace]
  refine ⟨200430312302448737561020175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133620208201632491707346783 200430312302448737561020175)
  ·
    refine ⟨300645468453673106341530263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200430312302448737561020175 300645468453673106341530263)
    ·
      refine ⟨450968202680509659512295395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300645468453673106341530263 450968202680509659512295395)
      ·
        refine ⟨676452304020764489268443093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450968202680509659512295395 676452304020764489268443093)
        ·
          refine ⟨15854350875486667717229135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 676452304020764489268443093 15854350875486667717229135)
          ·
            refine ⟨23781526313230001575843703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15854350875486667717229135 23781526313230001575843703)
            ·
              refine ⟨35672289469845002363765555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23781526313230001575843703 35672289469845002363765555)
              ·
                refine ⟨53508434204767503545648333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35672289469845002363765555 53508434204767503545648333)
                ·
                  refine ⟨20065662826787813829618125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53508434204767503545648333 20065662826787813829618125)
                  ·
                    refine ⟨7524623560045430186106797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20065662826787813829618125 7524623560045430186106797)
                    ·
                      refine ⟨2821733835017036319790049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7524623560045430186106797 2821733835017036319790049)
                      ·
                        rfl

theorem cell23_5495307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 3].length) (baseStart_5495307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495307 prefixEnd_5495307 := by exact prefixLift 5495307
  have htrace : WordTrace (prefixWord ++ tailWord_5495307) baseStart_5495307 baseEnd_5495307 := by
    simpa [prefixWord, tailWord_5495307, baseEnd_5495307] using wordTrace_append hprefix tailTrace_5495307
  have hstable : (prefixWord ++ tailWord_5495307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495307).length < 2 ^ (prefixWord ++ tailWord_5495307).sum := by decide
  have hdescent : baseEnd_5495307 < baseStart_5495307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495325 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_5495325 : Nat := 118140960795 + 5495325 * 2 ^ 59
def prefixEnd_5495325 : Nat := 4983230072969 + 3 ^ 40 * 5495325 * 2
def baseEnd_5495325 : Nat := 2821743077668817249364967

theorem tailTrace_5495325 : CollatzResearch.WordTrace tailWord_5495325 prefixEnd_5495325 2821743077668817249364967 := by
  unfold tailWord_5495325
  simp only [CollatzResearch.WordTrace]
  refine ⟨200430968816383526635175429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133620645877589017756783619 200430968816383526635175429)
  ·
    refine ⟨37580806653071911244095393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200430968816383526635175429 37580806653071911244095393)
    ·
      refine ⟨28185604989803933433071545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37580806653071911244095393 28185604989803933433071545)
      ·
        refine ⟨21139203742352950074803659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28185604989803933433071545 21139203742352950074803659)
        ·
          refine ⟨31708805613529425112205489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21139203742352950074803659 31708805613529425112205489)
          ·
            refine ⟨23781604210147068834154117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31708805613529425112205489 23781604210147068834154117)
            ·
              refine ⟨4459050789402575406403897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23781604210147068834154117 4459050789402575406403897)
              ·
                refine ⟨3344288092051931554802923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4459050789402575406403897 3344288092051931554802923)
                ·
                  refine ⟨5016432138077897332204385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344288092051931554802923 5016432138077897332204385)
                  ·
                    refine ⟨3762324103558422999153289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5016432138077897332204385 3762324103558422999153289)
                    ·
                      refine ⟨2821743077668817249364967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762324103558422999153289 2821743077668817249364967)
                      ·
                        rfl

theorem cell23_5495325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_5495325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495325 prefixEnd_5495325 := by exact prefixLift 5495325
  have htrace : WordTrace (prefixWord ++ tailWord_5495325) baseStart_5495325 baseEnd_5495325 := by
    simpa [prefixWord, tailWord_5495325, baseEnd_5495325] using wordTrace_append hprefix tailTrace_5495325
  have hstable : (prefixWord ++ tailWord_5495325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495325).length < 2 ^ (prefixWord ++ tailWord_5495325).sum := by decide
  have hdescent : baseEnd_5495325 < baseStart_5495325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495377 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_5495377 : Nat := 118140960795 + 5495377 * 2 ^ 59
def prefixEnd_5495377 : Nat := 4983230072969 + 3 ^ 40 * 5495377 * 2
def baseEnd_5495377 : Nat := 2821769778662851045914727

theorem tailTrace_5495377 : CollatzResearch.WordTrace tailWord_5495377 prefixEnd_5495377 2821769778662851045914727 := by
  unfold tailWord_5495377
  simp only [CollatzResearch.WordTrace]
  refine ⟨200432865412195139516068385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133621910274796759677378923 200432865412195139516068385)
  ·
    refine ⟨150324649059146354637051289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200432865412195139516068385 150324649059146354637051289)
    ·
      refine ⟨112743486794359765977788467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150324649059146354637051289 112743486794359765977788467)
      ·
        refine ⟨169115230191539648966682701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112743486794359765977788467 169115230191539648966682701)
        ·
          refine ⟨63418211321827368362506013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169115230191539648966682701 63418211321827368362506013)
          ·
            refine ⟨23781829245685263135939755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63418211321827368362506013 23781829245685263135939755)
            ·
              refine ⟨35672743868527894703909633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23781829245685263135939755 35672743868527894703909633)
              ·
                refine ⟨26754557901395921027932225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35672743868527894703909633 26754557901395921027932225)
                ·
                  refine ⟨20065918426046940770949169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26754557901395921027932225 20065918426046940770949169)
                  ·
                    refine ⟨15049438819535205578211877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20065918426046940770949169 15049438819535205578211877)
                    ·
                      refine ⟨2821769778662851045914727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15049438819535205578211877 2821769778662851045914727)
                      ·
                        rfl

theorem cell23_5495377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_5495377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495377 prefixEnd_5495377 := by exact prefixLift 5495377
  have htrace : WordTrace (prefixWord ++ tailWord_5495377) baseStart_5495377 baseEnd_5495377 := by
    simpa [prefixWord, tailWord_5495377, baseEnd_5495377] using wordTrace_append hprefix tailTrace_5495377
  have hstable : (prefixWord ++ tailWord_5495377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495377).length < 2 ^ (prefixWord ++ tailWord_5495377).sum := by decide
  have hdescent : baseEnd_5495377 < baseStart_5495377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495417 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_5495417 : Nat := 118140960795 + 5495417 * 2 ^ 59
def prefixEnd_5495417 : Nat := 4983230072969 + 3 ^ 40 * 5495417 * 2
def baseEnd_5495417 : Nat := 940596772629676963138181

theorem tailTrace_5495417 : CollatzResearch.WordTrace tailWord_5495417 prefixEnd_5495417 940596772629676963138181 := by
  unfold tailWord_5495417
  simp only [CollatzResearch.WordTrace]
  refine ⟨200434324332050226347524505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133622882888033484231683003 200434324332050226347524505)
  ·
    refine ⟨150325743249037669760643379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200434324332050226347524505 150325743249037669760643379)
    ·
      refine ⟨225488614873556504640965069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150325743249037669760643379 225488614873556504640965069)
      ·
        refine ⟨84558230577583689240361901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225488614873556504640965069 84558230577583689240361901)
        ·
          refine ⟨31709336466593883465135713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84558230577583689240361901 31709336466593883465135713)
          ·
            refine ⟨23782002349945412598851785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31709336466593883465135713 23782002349945412598851785)
            ·
              refine ⟨17836501762459059449138839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23782002349945412598851785 17836501762459059449138839)
              ·
                refine ⟨26754752643688589173708259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17836501762459059449138839 26754752643688589173708259)
                ·
                  refine ⟨40132128965532883760562389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26754752643688589173708259 40132128965532883760562389)
                  ·
                    refine ⟨940596772629676963138181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40132128965532883760562389 940596772629676963138181)
                    ·
                      rfl

theorem cell23_5495417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_5495417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495417 prefixEnd_5495417 := by exact prefixLift 5495417
  have htrace : WordTrace (prefixWord ++ tailWord_5495417) baseStart_5495417 baseEnd_5495417 := by
    simpa [prefixWord, tailWord_5495417, baseEnd_5495417] using wordTrace_append hprefix tailTrace_5495417
  have hstable : (prefixWord ++ tailWord_5495417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495417).length < 2 ^ (prefixWord ++ tailWord_5495417).sum := by decide
  have hdescent : baseEnd_5495417 < baseStart_5495417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495444 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5495444 : Nat := 118140960795 + 5495444 * 2 ^ 59
def prefixEnd_5495444 : Nat := 4983230072969 + 3 ^ 40 * 5495444 * 2
def baseEnd_5495444 : Nat := 2821804181866702283776919

theorem tailTrace_5495444 : CollatzResearch.WordTrace tailWord_5495444 prefixEnd_5495444 2821804181866702283776919 := by
  unfold tailWord_5495444
  simp only [CollatzResearch.WordTrace]
  refine ⟨100217654551476204979378693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133623539401968273305838257 100217654551476204979378693)
  ·
    refine ⟨18790810228401788433633505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100217654551476204979378693 18790810228401788433633505)
    ·
      refine ⟨14093107671301341325225129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18790810228401788433633505 14093107671301341325225129)
      ·
        refine ⟨10569830753476005993918847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14093107671301341325225129 10569830753476005993918847)
        ·
          refine ⟨15854746130214008990878271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10569830753476005993918847 15854746130214008990878271)
          ·
            refine ⟨23782119195321013486317407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15854746130214008990878271 23782119195321013486317407)
            ·
              refine ⟨35673178792981520229476111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23782119195321013486317407 35673178792981520229476111)
              ·
                refine ⟨53509768189472280344214167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35673178792981520229476111 53509768189472280344214167)
                ·
                  refine ⟨80264652284208420516321251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53509768189472280344214167 80264652284208420516321251)
                  ·
                    refine ⟨120396978426312630774481877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80264652284208420516321251 120396978426312630774481877)
                    ·
                      refine ⟨2821804181866702283776919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120396978426312630774481877 2821804181866702283776919)
                      ·
                        rfl

theorem cell23_5495444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5495444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495444 prefixEnd_5495444 := by exact prefixLift 5495444
  have htrace : WordTrace (prefixWord ++ tailWord_5495444) baseStart_5495444 baseEnd_5495444 := by
    simpa [prefixWord, tailWord_5495444, baseEnd_5495444] using wordTrace_append hprefix tailTrace_5495444
  have hstable : (prefixWord ++ tailWord_5495444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495444).length < 2 ^ (prefixWord ++ tailWord_5495444).sum := by decide
  have hdescent : baseEnd_5495444 < baseStart_5495444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495481 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 1, 4]
def baseStart_5495481 : Nat := 118140960795 + 5495481 * 2 ^ 59
def prefixEnd_5495481 : Nat := 4983230072969 + 3 ^ 40 * 5495481 * 2
def baseEnd_5495481 : Nat := 940607726883639546338083

theorem tailTrace_5495481 : CollatzResearch.WordTrace tailWord_5495481 prefixEnd_5495481 940607726883639546338083 := by
  unfold tailWord_5495481
  simp only [CollatzResearch.WordTrace]
  refine ⟨200436658603818365277854297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133624439069212243518569531 200436658603818365277854297)
  ·
    refine ⟨150327493952863773958390723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200436658603818365277854297 150327493952863773958390723)
    ·
      refine ⟨225491240929295660937586085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150327493952863773958390723 225491240929295660937586085)
      ·
        refine ⟨42279607674242936425797391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225491240929295660937586085 42279607674242936425797391)
        ·
          refine ⟨63419411511364404638696087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42279607674242936425797391 63419411511364404638696087)
          ·
            refine ⟨95129117267046606958044131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63419411511364404638696087 95129117267046606958044131)
            ·
              refine ⟨142693675900569910437066197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95129117267046606958044131 142693675900569910437066197)
              ·
                refine ⟨3344383028919607275868739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142693675900569910437066197 3344383028919607275868739)
                ·
                  refine ⟨5016574543379410913803109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344383028919607275868739 5016574543379410913803109)
                  ·
                    refine ⟨940607726883639546338083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016574543379410913803109 940607726883639546338083)
                    ·
                      rfl

theorem cell23_5495481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 4].length) (baseStart_5495481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495481 prefixEnd_5495481 := by exact prefixLift 5495481
  have htrace : WordTrace (prefixWord ++ tailWord_5495481) baseStart_5495481 baseEnd_5495481 := by
    simpa [prefixWord, tailWord_5495481, baseEnd_5495481] using wordTrace_append hprefix tailTrace_5495481
  have hstable : (prefixWord ++ tailWord_5495481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495481).length < 2 ^ (prefixWord ++ tailWord_5495481).sum := by decide
  have hdescent : baseEnd_5495481 < baseStart_5495481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495498 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_5495498 : Nat := 118140960795 + 5495498 * 2 ^ 59
def prefixEnd_5495498 : Nat := 4983230072969 + 3 ^ 40 * 5495498 * 2
def baseEnd_5495498 : Nat := 940610636607348357500557

theorem tailTrace_5495498 : CollatzResearch.WordTrace tailWord_5495498 prefixEnd_5495498 940610636607348357500557 := by
  unfold tailWord_5495498
  simp only [CollatzResearch.WordTrace]
  refine ⟨50109319661189194295305787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133624852429837851454148765 50109319661189194295305787)
  ·
    refine ⟨75163979491783791442958681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50109319661189194295305787 75163979491783791442958681)
    ·
      refine ⟨56372984618837843582219011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75163979491783791442958681 56372984618837843582219011)
      ·
        refine ⟨84559476928256765373328517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56372984618837843582219011 84559476928256765373328517)
        ·
          refine ⟨15854901924048143507499097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84559476928256765373328517 15854901924048143507499097)
          ·
            refine ⟨11891176443036107630624323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15854901924048143507499097 11891176443036107630624323)
            ·
              refine ⟨17836764664554161445936485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11891176443036107630624323 17836764664554161445936485)
              ·
                refine ⟨3344393374603905271113091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17836764664554161445936485 3344393374603905271113091)
                ·
                  refine ⟨5016590061905857906669637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344393374603905271113091 5016590061905857906669637)
                  ·
                    refine ⟨940610636607348357500557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016590061905857906669637 940610636607348357500557)
                    ·
                      rfl

theorem cell23_5495498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_5495498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495498 prefixEnd_5495498 := by exact prefixLift 5495498
  have htrace : WordTrace (prefixWord ++ tailWord_5495498) baseStart_5495498 baseEnd_5495498 := by
    simpa [prefixWord, tailWord_5495498, baseEnd_5495498] using wordTrace_append hprefix tailTrace_5495498
  have hstable : (prefixWord ++ tailWord_5495498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495498).length < 2 ^ (prefixWord ++ tailWord_5495498).sum := by decide
  have hdescent : baseEnd_5495498 < baseStart_5495498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495521 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_5495521 : Nat := 118140960795 + 5495521 * 2 ^ 59
def prefixEnd_5495521 : Nat := 4983230072969 + 3 ^ 40 * 5495521 * 2
def baseEnd_5495521 : Nat := 2821843719877098482514065

theorem tailTrace_5495521 : CollatzResearch.WordTrace tailWord_5495521 prefixEnd_5495521 2821843719877098482514065 := by
  unfold tailWord_5495521
  simp only [CollatzResearch.WordTrace]
  refine ⟨200438117523673452109310417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133625411682448968072873611 200438117523673452109310417)
  ·
    refine ⟨150328588142755089081982813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200438117523673452109310417 150328588142755089081982813)
    ·
      refine ⟨56373220553533158405743555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150328588142755089081982813 56373220553533158405743555)
      ·
        refine ⟨84559830830299737608615333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56373220553533158405743555 84559830830299737608615333)
        ·
          refine ⟨15854968280681200801615375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84559830830299737608615333 15854968280681200801615375)
          ·
            refine ⟨23782452421021801202423063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15854968280681200801615375 23782452421021801202423063)
            ·
              refine ⟨35673678631532701803634595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23782452421021801202423063 35673678631532701803634595)
              ·
                refine ⟨53510517947299052705451893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35673678631532701803634595 53510517947299052705451893)
                ·
                  refine ⟨5016611057559286191136115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53510517947299052705451893 5016611057559286191136115)
                  ·
                    refine ⟨7524916586338929286704173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5016611057559286191136115 7524916586338929286704173)
                    ·
                      refine ⟨2821843719877098482514065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7524916586338929286704173 2821843719877098482514065)
                      ·
                        rfl

theorem cell23_5495521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_5495521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495521 prefixEnd_5495521 := by exact prefixLift 5495521
  have htrace : WordTrace (prefixWord ++ tailWord_5495521) baseStart_5495521 baseEnd_5495521 := by
    simpa [prefixWord, tailWord_5495521, baseEnd_5495521] using wordTrace_append hprefix tailTrace_5495521
  have hstable : (prefixWord ++ tailWord_5495521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495521).length < 2 ^ (prefixWord ++ tailWord_5495521).sum := by decide
  have hdescent : baseEnd_5495521 < baseStart_5495521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495524 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_5495524 : Nat := 118140960795 + 5495524 * 2 ^ 59
def prefixEnd_5495524 : Nat := 4983230072969 + 3 ^ 40 * 5495524 * 2
def baseEnd_5495524 : Nat := 940615086773020656925517

theorem tailTrace_5495524 : CollatzResearch.WordTrace tailWord_5495524 prefixEnd_5495524 940615086773020656925517 := by
  unfold tailWord_5495524
  simp only [CollatzResearch.WordTrace]
  refine ⟨100219113471331291810834813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133625484628441722414446417 100219113471331291810834813)
  ·
    refine ⟨37582167551749234429063055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100219113471331291810834813 37582167551749234429063055)
    ·
      refine ⟨56373251327623851643594583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37582167551749234429063055 56373251327623851643594583)
      ·
        refine ⟨84559876991435777465391875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56373251327623851643594583 84559876991435777465391875)
        ·
          refine ⟨126839815487153666198087813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84559876991435777465391875 126839815487153666198087813)
          ·
            refine ⟨23782465403841312412141465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126839815487153666198087813 23782465403841312412141465)
            ·
              refine ⟨17836849052880984309106099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23782465403841312412141465 17836849052880984309106099)
              ·
                refine ⟨26755273579321476463659149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17836849052880984309106099 26755273579321476463659149)
                ·
                  refine ⟨10033227592245553673872181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26755273579321476463659149 10033227592245553673872181)
                  ·
                    refine ⟨940615086773020656925517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10033227592245553673872181 940615086773020656925517)
                    ·
                      rfl

theorem cell23_5495524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_5495524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495524 prefixEnd_5495524 := by exact prefixLift 5495524
  have htrace : WordTrace (prefixWord ++ tailWord_5495524) baseStart_5495524 baseEnd_5495524 := by
    simpa [prefixWord, tailWord_5495524, baseEnd_5495524] using wordTrace_append hprefix tailTrace_5495524
  have hstable : (prefixWord ++ tailWord_5495524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495524).length < 2 ^ (prefixWord ++ tailWord_5495524).sum := by decide
  have hdescent : baseEnd_5495524 < baseStart_5495524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495567 : List Nat := [1, 1, 2, 1, 1, 1, 6, 10]
def baseStart_5495567 : Nat := 118140960795 + 5495567 * 2 ^ 59
def prefixEnd_5495567 : Nat := 4983230072969 + 3 ^ 40 * 5495567 * 2
def baseEnd_5495567 : Nat := 104513605184711307501439

theorem tailTrace_5495567 : CollatzResearch.WordTrace tailWord_5495567 prefixEnd_5495567 104513605184711307501439 := by
  unfold tailWord_5495567
  simp only [CollatzResearch.WordTrace]
  refine ⟨200439795281506801965484955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133626530187671201310323303 200439795281506801965484955)
  ·
    refine ⟨300659692922260202948227433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200439795281506801965484955 300659692922260202948227433)
    ·
      refine ⟨225494769691695152211170575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300659692922260202948227433 225494769691695152211170575)
      ·
        refine ⟨338242154537542728316755863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225494769691695152211170575 338242154537542728316755863)
        ·
          refine ⟨507363231806314092475133795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338242154537542728316755863 507363231806314092475133795)
          ·
            refine ⟨761044847709471138712700693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507363231806314092475133795 761044847709471138712700693)
            ·
              refine ⟨35673977236381459627157845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 761044847709471138712700693 35673977236381459627157845)
              ·
                refine ⟨104513605184711307501439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35673977236381459627157845 104513605184711307501439)
                ·
                  rfl

theorem cell23_5495567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 10].length) (baseStart_5495567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495567 prefixEnd_5495567 := by exact prefixLift 5495567
  have htrace : WordTrace (prefixWord ++ tailWord_5495567) baseStart_5495567 baseEnd_5495567 := by
    simpa [prefixWord, tailWord_5495567, baseEnd_5495567] using wordTrace_append hprefix tailTrace_5495567
  have hstable : (prefixWord ++ tailWord_5495567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495567).length < 2 ^ (prefixWord ++ tailWord_5495567).sum := by decide
  have hdescent : baseEnd_5495567 < baseStart_5495567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495578 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2]
def baseStart_5495578 : Nat := 118140960795 + 5495578 * 2 ^ 59
def prefixEnd_5495578 : Nat := 4983230072969 + 3 ^ 40 * 5495578 * 2
def baseEnd_5495578 : Nat := 2821872988274404759501303

theorem tailTrace_5495578 : CollatzResearch.WordTrace tailWord_5495578 prefixEnd_5495578 2821872988274404759501303 := by
  unfold tailWord_5495578
  simp only [CollatzResearch.WordTrace]
  refine ⟨50110049121116737711033847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133626797656311300562756925 50110049121116737711033847)
  ·
    refine ⟨75165073681675106566550771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50110049121116737711033847 75165073681675106566550771)
    ·
      refine ⟨112747610522512659849826157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75165073681675106566550771 112747610522512659849826157)
      ·
        refine ⟨42280353945942247443684809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112747610522512659849826157 42280353945942247443684809)
        ·
          refine ⟨31710265459456685582763607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42280353945942247443684809 31710265459456685582763607)
          ·
            refine ⟨47565398189185028374145411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31710265459456685582763607 47565398189185028374145411)
            ·
              refine ⟨71348097283777542561218117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47565398189185028374145411 71348097283777542561218117)
              ·
                refine ⟨13377768240708289230228397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71348097283777542561218117 13377768240708289230228397)
                ·
                  refine ⟨5016663090265608461335649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13377768240708289230228397 5016663090265608461335649)
                  ·
                    refine ⟨3762497317699206346001737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5016663090265608461335649 3762497317699206346001737)
                    ·
                      refine ⟨2821872988274404759501303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762497317699206346001737 2821872988274404759501303)
                      ·
                        rfl

theorem cell23_5495578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_5495578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495578 prefixEnd_5495578 := by exact prefixLift 5495578
  have htrace : WordTrace (prefixWord ++ tailWord_5495578) baseStart_5495578 baseEnd_5495578 := by
    simpa [prefixWord, tailWord_5495578, baseEnd_5495578] using wordTrace_append hprefix tailTrace_5495578
  have hstable : (prefixWord ++ tailWord_5495578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495578).length < 2 ^ (prefixWord ++ tailWord_5495578).sum := by decide
  have hdescent : baseEnd_5495578 < baseStart_5495578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495584 : List Nat := [2, 1, 1, 5, 1, 3, 1, 9]
def baseStart_5495584 : Nat := 118140960795 + 5495584 * 2 ^ 59
def prefixEnd_5495584 : Nat := 4983230072969 + 3 ^ 40 * 5495584 * 2
def baseEnd_5495584 : Nat := 104513928487345619852825

theorem tailTrace_5495584 : CollatzResearch.WordTrace tailWord_5495584 prefixEnd_5495584 104513928487345619852825 := by
  unfold tailWord_5495584
  simp only [CollatzResearch.WordTrace]
  refine ⟨100220207661222606934426903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133626943548296809245902537 100220207661222606934426903)
  ·
    refine ⟨150330311491833910401640355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100220207661222606934426903 150330311491833910401640355)
    ·
      refine ⟨225495467237750865602460533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150330311491833910401640355 225495467237750865602460533)
      ·
        refine ⟨21140200053539143650230675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225495467237750865602460533 21140200053539143650230675)
        ·
          refine ⟨31710300080308715475346013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21140200053539143650230675 31710300080308715475346013)
          ·
            refine ⟨11891362530115768303254755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31710300080308715475346013 11891362530115768303254755)
            ·
              refine ⟨17837043795173652454882133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11891362530115768303254755 17837043795173652454882133)
              ·
                refine ⟨104513928487345619852825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17837043795173652454882133 104513928487345619852825)
                ·
                  rfl

theorem cell23_5495584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 9].length) (baseStart_5495584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495584 prefixEnd_5495584 := by exact prefixLift 5495584
  have htrace : WordTrace (prefixWord ++ tailWord_5495584) baseStart_5495584 baseEnd_5495584 := by
    simpa [prefixWord, tailWord_5495584, baseEnd_5495584] using wordTrace_append hprefix tailTrace_5495584
  have hstable : (prefixWord ++ tailWord_5495584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495584).length < 2 ^ (prefixWord ++ tailWord_5495584).sum := by decide
  have hdescent : baseEnd_5495584 < baseStart_5495584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495598 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5495598 : Nat := 118140960795 + 5495598 * 2 ^ 59
def prefixEnd_5495598 : Nat := 4983230072969 + 3 ^ 40 * 5495598 * 2
def baseEnd_5495598 : Nat := 2821883257887494681251211

theorem tailTrace_5495598 : CollatzResearch.WordTrace tailWord_5495598 prefixEnd_5495598 2821883257887494681251211 := by
  unfold tailWord_5495598
  simp only [CollatzResearch.WordTrace]
  refine ⟨25055115743049311782482931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133627283962929662839908965 25055115743049311782482931)
  ·
    refine ⟨37582673614573967673724397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25055115743049311782482931 37582673614573967673724397)
    ·
      refine ⟨14093502605465237877646649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37582673614573967673724397 14093502605465237877646649)
      ·
        refine ⟨10570126954098928408234987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14093502605465237877646649 10570126954098928408234987)
        ·
          refine ⟨15855190431148392612352481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10570126954098928408234987 15855190431148392612352481)
          ·
            refine ⟨11891392823361294459264361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15855190431148392612352481 11891392823361294459264361)
            ·
              refine ⟨8918544617520970844448271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11891392823361294459264361 8918544617520970844448271)
              ·
                refine ⟨13377816926281456266672407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8918544617520970844448271 13377816926281456266672407)
                ·
                  refine ⟨20066725389422184400008611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13377816926281456266672407 20066725389422184400008611)
                  ·
                    refine ⟨30100088084133276600012917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20066725389422184400008611 30100088084133276600012917)
                    ·
                      refine ⟨2821883257887494681251211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30100088084133276600012917 2821883257887494681251211)
                      ·
                        rfl

theorem cell23_5495598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5495598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495598 prefixEnd_5495598 := by exact prefixLift 5495598
  have htrace : WordTrace (prefixWord ++ tailWord_5495598) baseStart_5495598 baseEnd_5495598 := by
    simpa [prefixWord, tailWord_5495598, baseEnd_5495598] using wordTrace_append hprefix tailTrace_5495598
  have hstable : (prefixWord ++ tailWord_5495598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495598).length < 2 ^ (prefixWord ++ tailWord_5495598).sum := by decide
  have hdescent : baseEnd_5495598 < baseStart_5495598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495622 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_5495622 : Nat := 118140960795 + 5495622 * 2 ^ 59
def prefixEnd_5495622 : Nat := 4983230072969 + 3 ^ 40 * 5495622 * 2
def baseEnd_5495622 : Nat := 940631860474400862450367

theorem tailTrace_5495622 : CollatzResearch.WordTrace tailWord_5495622 prefixEnd_5495622 940631860474400862450367 := by
  unfold tailWord_5495622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6263806290509610823710535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133627867530871697572491413 6263806290509610823710535)
  ·
    refine ⟨9395709435764416235565803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6263806290509610823710535 9395709435764416235565803)
    ·
      refine ⟨14093564153646624353348705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395709435764416235565803 14093564153646624353348705)
      ·
        refine ⟨10570173115234968265011529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14093564153646624353348705 10570173115234968265011529)
        ·
          refine ⟨7927629836426226198758647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10570173115234968265011529 7927629836426226198758647)
          ·
            refine ⟨11891444754639339298137971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7927629836426226198758647 11891444754639339298137971)
            ·
              refine ⟨17837167131959008947206957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11891444754639339298137971 17837167131959008947206957)
              ·
                refine ⟨6688937674484628355202609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17837167131959008947206957 6688937674484628355202609)
                ·
                  refine ⟨5016703255863471266401957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6688937674484628355202609 5016703255863471266401957)
                  ·
                    refine ⟨940631860474400862450367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016703255863471266401957 940631860474400862450367)
                    ·
                      rfl

theorem cell23_5495622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_5495622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495622 prefixEnd_5495622 := by exact prefixLift 5495622
  have htrace : WordTrace (prefixWord ++ tailWord_5495622) baseStart_5495622 baseEnd_5495622 := by
    simpa [prefixWord, tailWord_5495622, baseEnd_5495622] using wordTrace_append hprefix tailTrace_5495622
  have hstable : (prefixWord ++ tailWord_5495622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495622).length < 2 ^ (prefixWord ++ tailWord_5495622).sum := by decide
  have hdescent : baseEnd_5495622 < baseStart_5495622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495662 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_5495662 : Nat := 118140960795 + 5495662 * 2 ^ 59
def prefixEnd_5495662 : Nat := 4983230072969 + 3 ^ 40 * 5495662 * 2
def baseEnd_5495662 : Nat := 2821916120649382430850917

theorem tailTrace_5495662 : CollatzResearch.WordTrace tailWord_5495662 prefixEnd_5495662 2821916120649382430850917 := by
  unfold tailWord_5495662
  simp only [CollatzResearch.WordTrace]
  refine ⟨25055407527020329148774155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133628840144108422126795493 25055407527020329148774155)
  ·
    refine ⟨37583111290530493723161233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25055407527020329148774155 37583111290530493723161233)
    ·
      refine ⟨28187333467897870292370925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37583111290530493723161233 28187333467897870292370925)
      ·
        refine ⟨10570250050461701359639097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28187333467897870292370925 10570250050461701359639097)
        ·
          refine ⟨7927687537846276019729323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10570250050461701359639097 7927687537846276019729323)
          ·
            refine ⟨11891531306769414029593985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7927687537846276019729323 11891531306769414029593985)
            ·
              refine ⟨8918648480077060522195489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11891531306769414029593985 8918648480077060522195489)
              ·
                refine ⟨6688986360057795391646617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8918648480077060522195489 6688986360057795391646617)
                ·
                  refine ⟨5016739770043346543734963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6688986360057795391646617 5016739770043346543734963)
                  ·
                    refine ⟨7525109655065019815602445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5016739770043346543734963 7525109655065019815602445)
                    ·
                      refine ⟨2821916120649382430850917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7525109655065019815602445 2821916120649382430850917)
                      ·
                        rfl

theorem cell23_5495662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_5495662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495662 prefixEnd_5495662 := by exact prefixLift 5495662
  have htrace : WordTrace (prefixWord ++ tailWord_5495662) baseStart_5495662 baseEnd_5495662 := by
    simpa [prefixWord, tailWord_5495662, baseEnd_5495662] using wordTrace_append hprefix tailTrace_5495662
  have hstable : (prefixWord ++ tailWord_5495662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495662).length < 2 ^ (prefixWord ++ tailWord_5495662).sum := by decide
  have hdescent : baseEnd_5495662 < baseStart_5495662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495674 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_5495674 : Nat := 118140960795 + 5495674 * 2 ^ 59
def prefixEnd_5495674 : Nat := 4983230072969 + 3 ^ 40 * 5495674 * 2
def baseEnd_5495674 : Nat := 313546920268581820433429

theorem tailTrace_5495674 : CollatzResearch.WordTrace tailWord_5495674 prefixEnd_5495674 313546920268581820433429 := by
  unfold tailWord_5495674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50110924473029789809907519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133629131928079439493086717 50110924473029789809907519)
  ·
    refine ⟨75166386709544684714861279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50110924473029789809907519 75166386709544684714861279)
    ·
      refine ⟨112749580064317027072291919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75166386709544684714861279 112749580064317027072291919)
      ·
        refine ⟨169124370096475540608437879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112749580064317027072291919 169124370096475540608437879)
        ·
          refine ⟨253686555144713310912656819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169124370096475540608437879 253686555144713310912656819)
          ·
            refine ⟨380529832717069966368985229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253686555144713310912656819 380529832717069966368985229)
            ·
              refine ⟨142698687268901237388369461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380529832717069966368985229 142698687268901237388369461)
              ·
                refine ⟨13378001931459491005159637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142698687268901237388369461 13378001931459491005159637)
                ·
                  refine ⟨313546920268581820433429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13378001931459491005159637 313546920268581820433429)
                  ·
                    rfl

theorem cell23_5495674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_5495674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495674 prefixEnd_5495674 := by exact prefixLift 5495674
  have htrace : WordTrace (prefixWord ++ tailWord_5495674) baseStart_5495674 baseEnd_5495674 := by
    simpa [prefixWord, tailWord_5495674, baseEnd_5495674] using wordTrace_append hprefix tailTrace_5495674
  have hstable : (prefixWord ++ tailWord_5495674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495674).length < 2 ^ (prefixWord ++ tailWord_5495674).sum := by decide
  have hdescent : baseEnd_5495674 < baseStart_5495674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495685 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 2, 2, 2]
def baseStart_5495685 : Nat := 118140960795 + 5495685 * 2 ^ 59
def prefixEnd_5495685 : Nat := 4983230072969 + 3 ^ 40 * 5495685 * 2
def baseEnd_5495685 : Nat := 2821927930704435840863311

theorem tailTrace_5495685 : CollatzResearch.WordTrace tailWord_5495685 prefixEnd_5495685 2821927930704435840863311 := by
  unfold tailWord_5495685
  simp only [CollatzResearch.WordTrace]
  refine ⟨200444099095079308118280509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133629399396719538745520339 200444099095079308118280509)
  ·
    refine ⟨75166537160654740544355191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200444099095079308118280509 75166537160654740544355191)
    ·
      refine ⟨112749805740982110816532787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75166537160654740544355191 112749805740982110816532787)
      ·
        refine ⟨169124708611473166224799181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112749805740982110816532787 169124708611473166224799181)
        ·
          refine ⟨63421765729302437334299693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169124708611473166224799181 63421765729302437334299693)
          ·
            refine ⟨23783162148488414000362385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63421765729302437334299693 23783162148488414000362385)
            ·
              refine ⟨17837371611366310500271789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23783162148488414000362385 17837371611366310500271789)
              ·
                refine ⟨6689014354262366437601921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17837371611366310500271789 6689014354262366437601921)
                ·
                  refine ⟨5016760765696774828201441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6689014354262366437601921 5016760765696774828201441)
                  ·
                    refine ⟨3762570574272581121151081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5016760765696774828201441 3762570574272581121151081)
                    ·
                      refine ⟨2821927930704435840863311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762570574272581121151081 2821927930704435840863311)
                      ·
                        rfl

theorem cell23_5495685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_5495685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495685 prefixEnd_5495685 := by exact prefixLift 5495685
  have htrace : WordTrace (prefixWord ++ tailWord_5495685) baseStart_5495685 baseEnd_5495685 := by
    simpa [prefixWord, tailWord_5495685, baseEnd_5495685] using wordTrace_append hprefix tailTrace_5495685
  have hstable : (prefixWord ++ tailWord_5495685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495685).length < 2 ^ (prefixWord ++ tailWord_5495685).sum := by decide
  have hdescent : baseEnd_5495685 < baseStart_5495685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495719 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_5495719 : Nat := 118140960795 + 5495719 * 2 ^ 59
def prefixEnd_5495719 : Nat := 4983230072969 + 3 ^ 40 * 5495719 * 2
def baseEnd_5495719 : Nat := 2821945389046688707838155

theorem tailTrace_5495719 : CollatzResearch.WordTrace tailWord_5495719 prefixEnd_5495719 2821945389046688707838155 := by
  unfold tailWord_5495719
  simp only [CollatzResearch.WordTrace]
  refine ⟨200445339176956131925018211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133630226117970754616678807 200445339176956131925018211)
  ·
    refine ⟨300668008765434197887527317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200445339176956131925018211 300668008765434197887527317)
    ·
      refine ⟨14093812910879728025977843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 300668008765434197887527317 14093812910879728025977843)
      ·
        refine ⟨21140719366319592038966765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14093812910879728025977843 21140719366319592038966765)
        ·
          refine ⟨7927769762369847014612537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21140719366319592038966765 7927769762369847014612537)
          ·
            refine ⟨5945827321777385260959403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7927769762369847014612537 5945827321777385260959403)
            ·
              refine ⟨8918740982666077891439105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5945827321777385260959403 8918740982666077891439105)
              ·
                refine ⟨6689055736999558418579329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8918740982666077891439105 6689055736999558418579329)
                ·
                  refine ⟨5016791802749668813934497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6689055736999558418579329 5016791802749668813934497)
                  ·
                    refine ⟨3762593852062251610450873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5016791802749668813934497 3762593852062251610450873)
                    ·
                      refine ⟨2821945389046688707838155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762593852062251610450873 2821945389046688707838155)
                      ·
                        rfl

theorem cell23_5495719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_5495719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495719 prefixEnd_5495719 := by exact prefixLift 5495719
  have htrace : WordTrace (prefixWord ++ tailWord_5495719) baseStart_5495719 baseEnd_5495719 := by
    simpa [prefixWord, tailWord_5495719, baseEnd_5495719] using wordTrace_append hprefix tailTrace_5495719
  have hstable : (prefixWord ++ tailWord_5495719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495719).length < 2 ^ (prefixWord ++ tailWord_5495719).sum := by decide
  have hdescent : baseEnd_5495719 < baseStart_5495719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495725 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 7]
def baseStart_5495725 : Nat := 118140960795 + 5495725 * 2 ^ 59
def prefixEnd_5495725 : Nat := 4983230072969 + 3 ^ 40 * 5495725 * 2
def baseEnd_5495725 : Nat := 313549829992290631595903

theorem tailTrace_5495725 : CollatzResearch.WordTrace tailWord_5495725 prefixEnd_5495725 313549829992290631595903 := by
  unfold tailWord_5495725
  simp only [CollatzResearch.WordTrace]
  refine ⟨200445558014934394949736629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133630372009956263299824419 200445558014934394949736629)
  ·
    refine ⟨18791771063900099526537809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200445558014934394949736629 18791771063900099526537809)
    ·
      refine ⟨14093828297925074644903357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18791771063900099526537809 14093828297925074644903357)
      ·
        refine ⟨5285185611721902991838759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14093828297925074644903357 5285185611721902991838759)
        ·
          refine ⟨7927778417582854487758139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5285185611721902991838759 7927778417582854487758139)
          ·
            refine ⟨11891667626374281731637209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7927778417582854487758139 11891667626374281731637209)
            ·
              refine ⟨8918750719780711298727907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11891667626374281731637209 8918750719780711298727907)
              ·
                refine ⟨13378126079671066948091861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8918750719780711298727907 13378126079671066948091861)
                ·
                  refine ⟨313549829992290631595903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13378126079671066948091861 313549829992290631595903)
                  ·
                    rfl

theorem cell23_5495725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_5495725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495725 prefixEnd_5495725 := by exact prefixLift 5495725
  have htrace : WordTrace (prefixWord ++ tailWord_5495725) baseStart_5495725 baseEnd_5495725 := by
    simpa [prefixWord, tailWord_5495725, baseEnd_5495725] using wordTrace_append hprefix tailTrace_5495725
  have hstable : (prefixWord ++ tailWord_5495725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495725).length < 2 ^ (prefixWord ++ tailWord_5495725).sum := by decide
  have hdescent : baseEnd_5495725 < baseStart_5495725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495761 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_5495761 : Nat := 118140960795 + 5495761 * 2 ^ 59
def prefixEnd_5495761 : Nat := 4983230072969 + 3 ^ 40 * 5495761 * 2
def baseEnd_5495761 : Nat := 2821966955234177543512961

theorem tailTrace_5495761 : CollatzResearch.WordTrace tailWord_5495761 prefixEnd_5495761 2821966955234177543512961 := by
  unfold tailWord_5495761
  simp only [CollatzResearch.WordTrace]
  refine ⟨200446871042803973098047137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133631247361869315398698091 200446871042803973098047137)
  ·
    refine ⟨150335153282102979823535353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200446871042803973098047137 150335153282102979823535353)
    ·
      refine ⟨112751364961577234867651515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150335153282102979823535353 112751364961577234867651515)
      ·
        refine ⟨169127047442365852301477273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112751364961577234867651515 169127047442365852301477273)
        ·
          refine ⟨126845285581774389226107955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169127047442365852301477273 126845285581774389226107955)
          ·
            refine ⟨190267928372661583839161933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126845285581774389226107955 190267928372661583839161933)
            ·
              refine ⟨71350473139748093939685725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190267928372661583839161933 71350473139748093939685725)
              ·
                refine ⟨26756427427405535227382147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71350473139748093939685725 26756427427405535227382147)
                ·
                  refine ⟨40134641141108302841073221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26756427427405535227382147 40134641141108302841073221)
                  ·
                    refine ⟨7525245213957806782701229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40134641141108302841073221 7525245213957806782701229)
                    ·
                      refine ⟨2821966955234177543512961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7525245213957806782701229 2821966955234177543512961)
                      ·
                        rfl

theorem cell23_5495761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_5495761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495761 prefixEnd_5495761 := by exact prefixLift 5495761
  have htrace : WordTrace (prefixWord ++ tailWord_5495761) baseStart_5495761 baseEnd_5495761 := by
    simpa [prefixWord, tailWord_5495761, baseEnd_5495761] using wordTrace_append hprefix tailTrace_5495761
  have hstable : (prefixWord ++ tailWord_5495761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495761).length < 2 ^ (prefixWord ++ tailWord_5495761).sum := by decide
  have hdescent : baseEnd_5495761 < baseStart_5495761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495836 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_5495836 : Nat := 118140960795 + 5495836 * 2 ^ 59
def prefixEnd_5495836 : Nat := 4983230072969 + 3 ^ 40 * 5495836 * 2
def baseEnd_5495836 : Nat := 940668488761088250025039

theorem tailTrace_5495836 : CollatzResearch.WordTrace tailWord_5495836 prefixEnd_5495836 940668488761088250025039 := by
  unfold tailWord_5495836
  simp only [CollatzResearch.WordTrace]
  refine ⟨100224803258766130453513681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133633071011688173938018241 100224803258766130453513681)
  ·
    refine ⟨75168602444074597840135261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100224803258766130453513681 75168602444074597840135261)
    ·
      refine ⟨28188225916527974190050723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75168602444074597840135261 28188225916527974190050723)
      ·
        refine ⟨42282338874791961285076085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28188225916527974190050723 42282338874791961285076085)
        ·
          refine ⟨3963969269511746370475883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42282338874791961285076085 3963969269511746370475883)
          ·
            refine ⟨5945953904267619555713825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963969269511746370475883 5945953904267619555713825)
            ·
              refine ⟨4459465428200714666785369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5945953904267619555713825 4459465428200714666785369)
              ·
                refine ⟨3344599071150536000089027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4459465428200714666785369 3344599071150536000089027)
                ·
                  refine ⟨5016898606725804000133541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344599071150536000089027 5016898606725804000133541)
                  ·
                    refine ⟨940668488761088250025039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016898606725804000133541 940668488761088250025039)
                    ·
                      rfl

theorem cell23_5495836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_5495836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495836 prefixEnd_5495836 := by exact prefixLift 5495836
  have htrace : WordTrace (prefixWord ++ tailWord_5495836) baseStart_5495836 baseEnd_5495836 := by
    simpa [prefixWord, tailWord_5495836, baseEnd_5495836] using wordTrace_append hprefix tailTrace_5495836
  have hstable : (prefixWord ++ tailWord_5495836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495836).length < 2 ^ (prefixWord ++ tailWord_5495836).sum := by decide
  have hdescent : baseEnd_5495836 < baseStart_5495836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495851 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5]
def baseStart_5495851 : Nat := 118140960795 + 5495851 * 2 ^ 59
def prefixEnd_5495851 : Nat := 4983230072969 + 3 ^ 40 * 5495851 * 2
def baseEnd_5495851 : Nat := 2822013168493082191387547

theorem tailTrace_5495851 : CollatzResearch.WordTrace tailWord_5495851 prefixEnd_5495851 2822013168493082191387547 := by
  unfold tailWord_5495851
  simp only [CollatzResearch.WordTrace]
  refine ⟨200450153612477918468823407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133633435741651945645882271 200450153612477918468823407)
  ·
    refine ⟨300675230418716877703235111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200450153612477918468823407 300675230418716877703235111)
    ·
      refine ⟨451012845628075316554852667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300675230418716877703235111 451012845628075316554852667)
      ·
        refine ⟨676519268442112974832279001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451012845628075316554852667 676519268442112974832279001)
        ·
          refine ⟨507389451331584731124209251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676519268442112974832279001 507389451331584731124209251)
          ·
            refine ⟨761084176997377096686313877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507389451331584731124209251 761084176997377096686313877)
            ·
              refine ⟨35675820796752051407170963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 761084176997377096686313877 35675820796752051407170963)
              ·
                refine ⟨53513731195128077110756445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35675820796752051407170963 53513731195128077110756445)
                ·
                  refine ⟨20067649198173028916533667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53513731195128077110756445 20067649198173028916533667)
                  ·
                    refine ⟨30101473797259543374800501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20067649198173028916533667 30101473797259543374800501)
                    ·
                      refine ⟨2822013168493082191387547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30101473797259543374800501 2822013168493082191387547)
                      ·
                        rfl

theorem cell23_5495851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_5495851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495851 prefixEnd_5495851 := by exact prefixLift 5495851
  have htrace : WordTrace (prefixWord ++ tailWord_5495851) baseStart_5495851 baseEnd_5495851 := by
    simpa [prefixWord, tailWord_5495851, baseEnd_5495851] using wordTrace_append hprefix tailTrace_5495851
  have hstable : (prefixWord ++ tailWord_5495851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495851).length < 2 ^ (prefixWord ++ tailWord_5495851).sum := by decide
  have hdescent : baseEnd_5495851 < baseStart_5495851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495858 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_5495858 : Nat := 118140960795 + 5495858 * 2 ^ 59
def prefixEnd_5495858 : Nat := 4983230072969 + 3 ^ 40 * 5495858 * 2
def baseEnd_5495858 : Nat := 940672254285887888000005

theorem tailTrace_5495858 : CollatzResearch.WordTrace tailWord_5495858 prefixEnd_5495858 940672254285887888000005 := by
  unfold tailWord_5495858
  simp only [CollatzResearch.WordTrace]
  refine ⟨50112602230863139666082057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133633605948968372442885485 50112602230863139666082057)
  ·
    refine ⟨37584451673147354749561543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50112602230863139666082057 37584451673147354749561543)
    ·
      refine ⟨56376677509721032124342315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37584451673147354749561543 56376677509721032124342315)
      ·
        refine ⟨84565016264581548186513473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56376677509721032124342315 84565016264581548186513473)
        ·
          refine ⟨63423762198436161139885105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84565016264581548186513473 63423762198436161139885105)
          ·
            refine ⟨47567821648827120854913829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63423762198436161139885105 47567821648827120854913829)
            ·
              refine ⟨8918966559155085160296343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47567821648827120854913829 8918966559155085160296343)
              ·
                refine ⟨13378449838732627740444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8918966559155085160296343 13378449838732627740444515)
                ·
                  refine ⟨20067674758098941610666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13378449838732627740444515 20067674758098941610666773)
                  ·
                    refine ⟨940672254285887888000005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20067674758098941610666773 940672254285887888000005)
                    ·
                      rfl

theorem cell23_5495858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_5495858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495858 prefixEnd_5495858 := by exact prefixLift 5495858
  have htrace : WordTrace (prefixWord ++ tailWord_5495858) baseStart_5495858 baseEnd_5495858 := by
    simpa [prefixWord, tailWord_5495858, baseEnd_5495858] using wordTrace_append hprefix tailTrace_5495858
  have hstable : (prefixWord ++ tailWord_5495858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495858).length < 2 ^ (prefixWord ++ tailWord_5495858).sum := by decide
  have hdescent : baseEnd_5495858 < baseStart_5495858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495902 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5495902 : Nat := 118140960795 + 5495902 * 2 ^ 59
def prefixEnd_5495902 : Nat := 4983230072969 + 3 ^ 40 * 5495902 * 2
def baseEnd_5495902 : Nat := 2822039356006461491849813

theorem tailTrace_5495902 : CollatzResearch.WordTrace tailWord_5495902 prefixEnd_5495902 2822039356006461491849813 := by
  unfold tailWord_5495902
  simp only [CollatzResearch.WordTrace]
  refine ⟨25056501716911644272366245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133634675823528769452619973 25056501716911644272366245)
  ·
    refine ⟨4698094071920933301068671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25056501716911644272366245 4698094071920933301068671)
    ·
      refine ⟨7047141107881399951603007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4698094071920933301068671 7047141107881399951603007)
      ·
        refine ⟨10570711661822099927404511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7047141107881399951603007 10570711661822099927404511)
        ·
          refine ⟨15856067492733149891106767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10570711661822099927404511 15856067492733149891106767)
          ·
            refine ⟨23784101239099724836660151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15856067492733149891106767 23784101239099724836660151)
            ·
              refine ⟨35676151858649587254990227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23784101239099724836660151 35676151858649587254990227)
              ·
                refine ⟨53514227787974380882485341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35676151858649587254990227 53514227787974380882485341)
                ·
                  refine ⟨20067835420490392830932003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53514227787974380882485341 20067835420490392830932003)
                  ·
                    refine ⟨30101753130735589246398005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20067835420490392830932003 30101753130735589246398005)
                    ·
                      refine ⟨2822039356006461491849813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30101753130735589246398005 2822039356006461491849813)
                      ·
                        rfl

theorem cell23_5495902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5495902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495902 prefixEnd_5495902 := by exact prefixLift 5495902
  have htrace : WordTrace (prefixWord ++ tailWord_5495902) baseStart_5495902 baseEnd_5495902 := by
    simpa [prefixWord, tailWord_5495902, baseEnd_5495902] using wordTrace_append hprefix tailTrace_5495902
  have hstable : (prefixWord ++ tailWord_5495902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495902).length < 2 ^ (prefixWord ++ tailWord_5495902).sum := by decide
  have hdescent : baseEnd_5495902 < baseStart_5495902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495921 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_5495921 : Nat := 118140960795 + 5495921 * 2 ^ 59
def prefixEnd_5495921 : Nat := 4983230072969 + 3 ^ 40 * 5495921 * 2
def baseEnd_5495921 : Nat := 2822049112138896917512225

theorem tailTrace_5495921 : CollatzResearch.WordTrace tailWord_5495921 prefixEnd_5495921 2822049112138896917512225 := by
  unfold tailWord_5495921
  simp only [CollatzResearch.WordTrace]
  refine ⟨200452706722224320423871617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133635137814816213615914411 200452706722224320423871617)
  ·
    refine ⟨150339530041668240317903713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200452706722224320423871617 150339530041668240317903713)
    ·
      refine ⟨112754647531251180238427785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150339530041668240317903713 112754647531251180238427785)
      ·
        refine ⟨84565985648438385178820839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112754647531251180238427785 84565985648438385178820839)
        ·
          refine ⟨126848978472657577768231259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84565985648438385178820839 126848978472657577768231259)
          ·
            refine ⟨190273467708986366652346889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126848978472657577768231259 190273467708986366652346889)
            ·
              refine ⟨142705100781739774989260167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190273467708986366652346889 142705100781739774989260167)
              ·
                refine ⟨214057651172609662483890251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142705100781739774989260167 214057651172609662483890251)
                ·
                  refine ⟨321086476758914493725835377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214057651172609662483890251 321086476758914493725835377)
                  ·
                    refine ⟨240814857569185870294376533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321086476758914493725835377 240814857569185870294376533)
                    ·
                      refine ⟨2822049112138896917512225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 240814857569185870294376533 2822049112138896917512225)
                      ·
                        rfl

theorem cell23_5495921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_5495921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495921 prefixEnd_5495921 := by exact prefixLift 5495921
  have htrace : WordTrace (prefixWord ++ tailWord_5495921) baseStart_5495921 baseEnd_5495921 := by
    simpa [prefixWord, tailWord_5495921, baseEnd_5495921] using wordTrace_append hprefix tailTrace_5495921
  have hstable : (prefixWord ++ tailWord_5495921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495921).length < 2 ^ (prefixWord ++ tailWord_5495921).sum := by decide
  have hdescent : baseEnd_5495921 < baseStart_5495921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495931 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 8]
def baseStart_5495931 : Nat := 118140960795 + 5495931 * 2 ^ 59
def prefixEnd_5495931 : Nat := 4983230072969 + 3 ^ 40 * 5495931 * 2
def baseEnd_5495931 : Nat := 940684748981813959462393

theorem tailTrace_5495931 : CollatzResearch.WordTrace tailWord_5495931 prefixEnd_5495931 940684748981813959462393 := by
  unfold tailWord_5495931
  simp only [CollatzResearch.WordTrace]
  refine ⟨200453071452188092131735647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133635380968125394754490431 200453071452188092131735647)
  ·
    refine ⟨300679607178282138197603471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200453071452188092131735647 300679607178282138197603471)
    ·
      refine ⟨451019410767423207296405207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300679607178282138197603471 451019410767423207296405207)
      ·
        refine ⟨676529116151134810944607811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451019410767423207296405207 676529116151134810944607811)
        ·
          refine ⟨1014793674226702216416911717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676529116151134810944607811 1014793674226702216416911717)
          ·
            refine ⟨190273813917506665578170947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1014793674226702216416911717 190273813917506665578170947)
            ·
              refine ⟨285410720876259998367256421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190273813917506665578170947 285410720876259998367256421)
              ·
                refine ⟨53514510164298749693860579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285410720876259998367256421 53514510164298749693860579)
                ·
                  refine ⟨80271765246448124540790869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53514510164298749693860579 80271765246448124540790869)
                  ·
                    refine ⟨940684748981813959462393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80271765246448124540790869 940684748981813959462393)
                    ·
                      rfl

theorem cell23_5495931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_5495931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495931 prefixEnd_5495931 := by exact prefixLift 5495931
  have htrace : WordTrace (prefixWord ++ tailWord_5495931) baseStart_5495931 baseEnd_5495931 := by
    simpa [prefixWord, tailWord_5495931, baseEnd_5495931] using wordTrace_append hprefix tailTrace_5495931
  have hstable : (prefixWord ++ tailWord_5495931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495931).length < 2 ^ (prefixWord ++ tailWord_5495931).sum := by decide
  have hdescent : baseEnd_5495931 < baseStart_5495931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495966 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_5495966 : Nat := 118140960795 + 5495966 * 2 ^ 59
def prefixEnd_5495966 : Nat := 4983230072969 + 3 ^ 40 * 5495966 * 2
def baseEnd_5495966 : Nat := 2822072218768349241449519

theorem tailTrace_5495966 : CollatzResearch.WordTrace tailWord_5495966 prefixEnd_5495966 2822072218768349241449519 := by
  unfold tailWord_5495966
  simp only [CollatzResearch.WordTrace]
  refine ⟨25056793500882661638657469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133636232004707528739506501 25056793500882661638657469)
  ·
    refine ⟨9396297562830998114496551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25056793500882661638657469 9396297562830998114496551)
    ·
      refine ⟨14094446344246497171744827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396297562830998114496551 14094446344246497171744827)
      ·
        refine ⟨21141669516369745757617241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14094446344246497171744827 21141669516369745757617241)
        ·
          refine ⟨15856252137277309318212931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21141669516369745757617241 15856252137277309318212931)
          ·
            refine ⟨23784378205915963977319397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15856252137277309318212931 23784378205915963977319397)
            ·
              refine ⟨4459570913609243245747387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23784378205915963977319397 4459570913609243245747387)
              ·
                refine ⟨6689356370413864868621081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4459570913609243245747387 6689356370413864868621081)
                ·
                  refine ⟨5017017277810398651465811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6689356370413864868621081 5017017277810398651465811)
                  ·
                    refine ⟨7525525916715597977198717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017017277810398651465811 7525525916715597977198717)
                    ·
                      refine ⟨2822072218768349241449519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7525525916715597977198717 2822072218768349241449519)
                      ·
                        rfl

theorem cell23_5495966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_5495966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495966 prefixEnd_5495966 := by exact prefixLift 5495966
  have htrace : WordTrace (prefixWord ++ tailWord_5495966) baseStart_5495966 baseEnd_5495966 := by
    simpa [prefixWord, tailWord_5495966, baseEnd_5495966] using wordTrace_append hprefix tailTrace_5495966
  have hstable : (prefixWord ++ tailWord_5495966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495966).length < 2 ^ (prefixWord ++ tailWord_5495966).sum := by decide
  have hdescent : baseEnd_5495966 < baseStart_5495966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495968 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5495968 : Nat := 118140960795 + 5495968 * 2 ^ 59
def prefixEnd_5495968 : Nat := 4983230072969 + 3 ^ 40 * 5495968 * 2
def baseEnd_5495968 : Nat := 2822073245729658233624509

theorem tailTrace_5495968 : CollatzResearch.WordTrace tailWord_5495968 prefixEnd_5495968 2822073245729658233624509 := by
  unfold tailWord_5495968
  simp only [CollatzResearch.WordTrace]
  refine ⟨100227210476527023725416279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133636280635369364967221705 100227210476527023725416279)
  ·
    refine ⟨150340815714790535588124419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100227210476527023725416279 150340815714790535588124419)
    ·
      refine ⟨225511223572185803382186629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150340815714790535588124419 225511223572185803382186629)
      ·
        refine ⟨42283354419784838134159993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225511223572185803382186629 42283354419784838134159993)
        ·
          refine ⟨31712515814838628600619995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42283354419784838134159993 31712515814838628600619995)
          ·
            refine ⟨47568773722257942900929993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31712515814838628600619995 47568773722257942900929993)
            ·
              refine ⟨35676580291693457175697495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47568773722257942900929993 35676580291693457175697495)
              ·
                refine ⟨53514870437540185763546243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35676580291693457175697495 53514870437540185763546243)
                ·
                  refine ⟨80272305656310278645319365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53514870437540185763546243 80272305656310278645319365)
                  ·
                    refine ⟨15051057310558177245997381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80272305656310278645319365 15051057310558177245997381)
                    ·
                      refine ⟨2822073245729658233624509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15051057310558177245997381 2822073245729658233624509)
                      ·
                        rfl

theorem cell23_5495968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5495968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495968 prefixEnd_5495968 := by exact prefixLift 5495968
  have htrace : WordTrace (prefixWord ++ tailWord_5495968) baseStart_5495968 baseEnd_5495968 := by
    simpa [prefixWord, tailWord_5495968, baseEnd_5495968] using wordTrace_append hprefix tailTrace_5495968
  have hstable : (prefixWord ++ tailWord_5495968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495968).length < 2 ^ (prefixWord ++ tailWord_5495968).sum := by decide
  have hdescent : baseEnd_5495968 < baseStart_5495968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5495975 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5495975 : Nat := 118140960795 + 5495975 * 2 ^ 59
def prefixEnd_5495975 : Nat := 4983230072969 + 3 ^ 40 * 5495975 * 2
def baseEnd_5495975 : Nat := 2822076840094239706236977

theorem tailTrace_5495975 : CollatzResearch.WordTrace tailWord_5495975 prefixEnd_5495975 2822076840094239706236977 := by
  unfold tailWord_5495975
  simp only [CollatzResearch.WordTrace]
  refine ⟨200454676264028687646337379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133636450842685791764224919 200454676264028687646337379)
  ·
    refine ⟨300682014396043031469506069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200454676264028687646337379 300682014396043031469506069)
    ·
      refine ⟨14094469424814517100133097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 300682014396043031469506069 14094469424814517100133097)
      ·
        refine ⟨10570852068610887825099823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14094469424814517100133097 10570852068610887825099823)
        ·
          refine ⟨15856278102916331737649735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10570852068610887825099823 15856278102916331737649735)
          ·
            refine ⟨23784417154374497606474603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15856278102916331737649735 23784417154374497606474603)
            ·
              refine ⟨35676625731561746409711905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23784417154374497606474603 35676625731561746409711905)
              ·
                refine ⟨26757469298671309807283929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35676625731561746409711905 26757469298671309807283929)
                ·
                  refine ⟨20068101974003482355462947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26757469298671309807283929 20068101974003482355462947)
                  ·
                    refine ⟨30102152961005223533194421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20068101974003482355462947 30102152961005223533194421)
                    ·
                      refine ⟨2822076840094239706236977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30102152961005223533194421 2822076840094239706236977)
                      ·
                        rfl

theorem cell23_5495975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5495975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5495975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5495975 prefixEnd_5495975 := by exact prefixLift 5495975
  have htrace : WordTrace (prefixWord ++ tailWord_5495975) baseStart_5495975 baseEnd_5495975 := by
    simpa [prefixWord, tailWord_5495975, baseEnd_5495975] using wordTrace_append hprefix tailTrace_5495975
  have hstable : (prefixWord ++ tailWord_5495975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5495975).length < 2 ^ (prefixWord ++ tailWord_5495975).sum := by decide
  have hdescent : baseEnd_5495975 < baseStart_5495975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5495975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496042 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_5496042 : Nat := 118140960795 + 5496042 * 2 ^ 59
def prefixEnd_5496042 : Nat := 4983230072969 + 3 ^ 40 * 5496042 * 2
def baseEnd_5496042 : Nat := 940703747766030314699723

theorem tailTrace_5496042 : CollatzResearch.WordTrace tailWord_5496042 prefixEnd_5496042 940703747766030314699723 := by
  unfold tailWord_5496042
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114279988696489522256595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133638079969857305392684253 50114279988696489522256595)
  ·
    refine ⟨75171419983044734283384893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50114279988696489522256595 75171419983044734283384893)
    ·
      refine ⟨28189282493641775356269335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75171419983044734283384893 28189282493641775356269335)
      ·
        refine ⟨42283923740462663034404003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28189282493641775356269335 42283923740462663034404003)
        ·
          refine ⟨63425885610693994551606005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42283923740462663034404003 63425885610693994551606005)
          ·
            refine ⟨5946176776002561989213063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63425885610693994551606005 5946176776002561989213063)
            ·
              refine ⟨8919265164003842983819595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946176776002561989213063 8919265164003842983819595)
              ·
                refine ⟨13378897746005764475729393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919265164003842983819595 13378897746005764475729393)
                ·
                  refine ⟨10034173309504323356797045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13378897746005764475729393 10034173309504323356797045)
                  ·
                    refine ⟨940703747766030314699723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10034173309504323356797045 940703747766030314699723)
                    ·
                      rfl

theorem cell23_5496042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_5496042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496042 prefixEnd_5496042 := by exact prefixLift 5496042
  have htrace : WordTrace (prefixWord ++ tailWord_5496042) baseStart_5496042 baseEnd_5496042 := by
    simpa [prefixWord, tailWord_5496042, baseEnd_5496042] using wordTrace_append hprefix tailTrace_5496042
  have hstable : (prefixWord ++ tailWord_5496042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496042).length < 2 ^ (prefixWord ++ tailWord_5496042).sum := by decide
  have hdescent : baseEnd_5496042 < baseStart_5496042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496058 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_5496058 : Nat := 118140960795 + 5496058 * 2 ^ 59
def prefixEnd_5496058 : Nat := 4983230072969 + 3 ^ 40 * 5496058 * 2
def baseEnd_5496058 : Nat := 2822119458988562881499095

theorem tailTrace_5496058 : CollatzResearch.WordTrace tailWord_5496058 prefixEnd_5496058 2822119458988562881499095 := by
  unfold tailWord_5496058
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114425880681998205402207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133638469015151995214405885 50114425880681998205402207)
  ·
    refine ⟨75171638821022997308103311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50114425880681998205402207 75171638821022997308103311)
    ·
      refine ⟨112757458231534495962154967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75171638821022997308103311 112757458231534495962154967)
      ·
        refine ⟨169136187347301743943232451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112757458231534495962154967 169136187347301743943232451)
        ·
          refine ⟨253704281020952615914848677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169136187347301743943232451 253704281020952615914848677)
          ·
            refine ⟨47569552691428615484034127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253704281020952615914848677 47569552691428615484034127)
            ·
              refine ⟨71354329037142923226051191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47569552691428615484034127 71354329037142923226051191)
              ·
                refine ⟨107031493555714384839076787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71354329037142923226051191 107031493555714384839076787)
                ·
                  refine ⟨160547240333571577258615181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107031493555714384839076787 160547240333571577258615181)
                  ·
                    refine ⟨60205215125089341471980693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160547240333571577258615181 60205215125089341471980693)
                    ·
                      refine ⟨2822119458988562881499095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60205215125089341471980693 2822119458988562881499095)
                      ·
                        rfl

theorem cell23_5496058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_5496058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496058 prefixEnd_5496058 := by exact prefixLift 5496058
  have htrace : WordTrace (prefixWord ++ tailWord_5496058) baseStart_5496058 baseEnd_5496058 := by
    simpa [prefixWord, tailWord_5496058, baseEnd_5496058] using wordTrace_append hprefix tailTrace_5496058
  have hstable : (prefixWord ++ tailWord_5496058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496058).length < 2 ^ (prefixWord ++ tailWord_5496058).sum := by decide
  have hdescent : baseEnd_5496058 < baseStart_5496058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496106 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_5496106 : Nat := 118140960795 + 5496106 * 2 ^ 59
def prefixEnd_5496106 : Nat := 4983230072969 + 3 ^ 40 * 5496106 * 2
def baseEnd_5496106 : Nat := 940714702019992897899625

theorem tailTrace_5496106 : CollatzResearch.WordTrace tailWord_5496106 prefixEnd_5496106 940714702019992897899625 := by
  unfold tailWord_5496106
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114863556638524254839043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133639636151036064679570781 50114863556638524254839043)
  ·
    refine ⟨75172295334957786382258565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50114863556638524254839043 75172295334957786382258565)
    ·
      refine ⟨14094805375304584946673481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75172295334957786382258565 14094805375304584946673481)
      ·
        refine ⟨10571104031478438710005111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14094805375304584946673481 10571104031478438710005111)
        ·
          refine ⟨15856656047217658065007667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10571104031478438710005111 15856656047217658065007667)
          ·
            refine ⟨23784984070826487097511501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15856656047217658065007667 23784984070826487097511501)
            ·
              refine ⟨8919369026559932661566813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23784984070826487097511501 8919369026559932661566813)
              ·
                refine ⟨3344763384959974748087555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8919369026559932661566813 3344763384959974748087555)
                ·
                  refine ⟨5017145077439962122131333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344763384959974748087555 5017145077439962122131333)
                  ·
                    refine ⟨940714702019992897899625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5017145077439962122131333 940714702019992897899625)
                    ·
                      rfl

theorem cell23_5496106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_5496106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496106 prefixEnd_5496106 := by exact prefixLift 5496106
  have htrace : WordTrace (prefixWord ++ tailWord_5496106) baseStart_5496106 baseEnd_5496106 := by
    simpa [prefixWord, tailWord_5496106, baseEnd_5496106] using wordTrace_append hprefix tailTrace_5496106
  have hstable : (prefixWord ++ tailWord_5496106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496106).length < 2 ^ (prefixWord ++ tailWord_5496106).sum := by decide
  have hdescent : baseEnd_5496106 < baseStart_5496106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496145 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_5496145 : Nat := 118140960795 + 5496145 * 2 ^ 59
def prefixEnd_5496145 : Nat := 4983230072969 + 3 ^ 40 * 5496145 * 2
def baseEnd_5496145 : Nat := 940721377268501347037065

theorem tailTrace_5496145 : CollatzResearch.WordTrace tailWord_5496145 prefixEnd_5496145 940721377268501347037065 := by
  unfold tailWord_5496145
  simp only [CollatzResearch.WordTrace]
  refine ⟨200460876673412806680025889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133640584448941871120017259 200460876673412806680025889)
  ·
    refine ⟨150345657505059605010019417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200460876673412806680025889 150345657505059605010019417)
    ·
      refine ⟨112759243128794703757514563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150345657505059605010019417 112759243128794703757514563)
      ·
        refine ⟨169138864693192055636271845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112759243128794703757514563 169138864693192055636271845)
        ·
          refine ⟨31713537129973510431800971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169138864693192055636271845 31713537129973510431800971)
          ·
            refine ⟨47570305694960265647701457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31713537129973510431800971 47570305694960265647701457)
            ·
              refine ⟨35677729271220199235776093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47570305694960265647701457 35677729271220199235776093)
              ·
                refine ⟨13379148476707574713416035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35677729271220199235776093 13379148476707574713416035)
                ·
                  refine ⟨20068722715061362070124053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13379148476707574713416035 20068722715061362070124053)
                  ·
                    refine ⟨940721377268501347037065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20068722715061362070124053 940721377268501347037065)
                    ·
                      rfl

theorem cell23_5496145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_5496145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496145 prefixEnd_5496145 := by exact prefixLift 5496145
  have htrace : WordTrace (prefixWord ++ tailWord_5496145) baseStart_5496145 baseEnd_5496145 := by
    simpa [prefixWord, tailWord_5496145, baseEnd_5496145] using wordTrace_append hprefix tailTrace_5496145
  have hstable : (prefixWord ++ tailWord_5496145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496145).length < 2 ^ (prefixWord ++ tailWord_5496145).sum := by decide
  have hdescent : baseEnd_5496145 < baseStart_5496145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496149 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_5496149 : Nat := 118140960795 + 5496149 * 2 ^ 59
def prefixEnd_5496149 : Nat := 4983230072969 + 3 ^ 40 * 5496149 * 2
def baseEnd_5496149 : Nat := 940722061909374008487059

theorem tailTrace_5496149 : CollatzResearch.WordTrace tailWord_5496149 prefixEnd_5496149 940722061909374008487059 := by
  unfold tailWord_5496149
  simp only [CollatzResearch.WordTrace]
  refine ⟨200461022565398315363171501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133640681710265543575447667 200461022565398315363171501)
  ·
    refine ⟨75172883462024368261189313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200461022565398315363171501 75172883462024368261189313)
    ·
      refine ⟨56379662596518276195891985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75172883462024368261189313 56379662596518276195891985)
      ·
        refine ⟨42284746947388707146918989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56379662596518276195891985 42284746947388707146918989)
        ·
          refine ⟨15856780105270765180094621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42284746947388707146918989 15856780105270765180094621)
          ·
            refine ⟨5946292539476536942535483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15856780105270765180094621 5946292539476536942535483)
            ·
              refine ⟨8919438809214805413803225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946292539476536942535483 8919438809214805413803225)
              ·
                refine ⟨6689579106911104060352419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8919438809214805413803225 6689579106911104060352419)
                ·
                  refine ⟨10034368660366656090528629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6689579106911104060352419 10034368660366656090528629)
                  ·
                    refine ⟨940722061909374008487059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10034368660366656090528629 940722061909374008487059)
                    ·
                      rfl

theorem cell23_5496149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_5496149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496149 prefixEnd_5496149 := by exact prefixLift 5496149
  have htrace : WordTrace (prefixWord ++ tailWord_5496149) baseStart_5496149 baseEnd_5496149 := by
    simpa [prefixWord, tailWord_5496149, baseEnd_5496149] using wordTrace_append hprefix tailTrace_5496149
  have hstable : (prefixWord ++ tailWord_5496149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496149).length < 2 ^ (prefixWord ++ tailWord_5496149).sum := by decide
  have hdescent : baseEnd_5496149 < baseStart_5496149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496150 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5496150 : Nat := 118140960795 + 5496150 * 2 ^ 59
def prefixEnd_5496150 : Nat := 4983230072969 + 3 ^ 40 * 5496150 * 2
def baseEnd_5496150 : Nat := 2822166699208776521548673

theorem tailTrace_5496150 : CollatzResearch.WordTrace tailWord_5496150 prefixEnd_5496150 2822166699208776521548673 := by
  unfold tailWord_5496150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12528816189899668283372369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133640706025596461689305269 12528816189899668283372369)
  ·
    refine ⟨9396612142424751212529277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12528816189899668283372369 9396612142424751212529277)
    ·
      refine ⟨3523729553409281704698479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9396612142424751212529277 3523729553409281704698479)
      ·
        refine ⟨5285594330113922557047719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3523729553409281704698479 5285594330113922557047719)
        ·
          refine ⟨7928391495170883835571579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5285594330113922557047719 7928391495170883835571579)
          ·
            refine ⟨11892587242756325753357369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7928391495170883835571579 11892587242756325753357369)
            ·
              refine ⟨8919440432067244315018027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11892587242756325753357369 8919440432067244315018027)
              ·
                refine ⟨13379160648100866472527041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919440432067244315018027 13379160648100866472527041)
                ·
                  refine ⟨10034370486075649854395281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13379160648100866472527041 10034370486075649854395281)
                  ·
                    refine ⟨7525777864556737390796461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10034370486075649854395281 7525777864556737390796461)
                    ·
                      refine ⟨2822166699208776521548673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7525777864556737390796461 2822166699208776521548673)
                      ·
                        rfl

theorem cell23_5496150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5496150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496150 prefixEnd_5496150 := by exact prefixLift 5496150
  have htrace : WordTrace (prefixWord ++ tailWord_5496150) baseStart_5496150 baseEnd_5496150 := by
    simpa [prefixWord, tailWord_5496150, baseEnd_5496150] using wordTrace_append hprefix tailTrace_5496150
  have hstable : (prefixWord ++ tailWord_5496150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496150).length < 2 ^ (prefixWord ++ tailWord_5496150).sum := by decide
  have hdescent : baseEnd_5496150 < baseStart_5496150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496162 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5496162 : Nat := 118140960795 + 5496162 * 2 ^ 59
def prefixEnd_5496162 : Nat := 4983230072969 + 3 ^ 40 * 5496162 * 2
def baseEnd_5496162 : Nat := 940724286992210158199539

theorem tailTrace_5496162 : CollatzResearch.WordTrace tailWord_5496162 prefixEnd_5496162 940724286992210158199539 := by
  unfold tailWord_5496162
  simp only [CollatzResearch.WordTrace]
  refine ⟨50115374178587804645848685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133640997809567479055596493 50115374178587804645848685)
  ·
    refine ⟨18793265316970426742193257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50115374178587804645848685 18793265316970426742193257)
    ·
      refine ⟨14094948987727820056644943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18793265316970426742193257 14094948987727820056644943)
      ·
        refine ⟨21142423481591730084967415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14094948987727820056644943 21142423481591730084967415)
        ·
          refine ⟨31713635222387595127451123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21142423481591730084967415 31713635222387595127451123)
          ·
            refine ⟨47570452833581392691176685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31713635222387595127451123 47570452833581392691176685)
            ·
              refine ⟨17838919812593022259191257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47570452833581392691176685 17838919812593022259191257)
              ·
                refine ⟨13379189859444766694393443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17838919812593022259191257 13379189859444766694393443)
                ·
                  refine ⟨20068784789167150041590165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13379189859444766694393443 20068784789167150041590165)
                  ·
                    refine ⟨940724286992210158199539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20068784789167150041590165 940724286992210158199539)
                    ·
                      rfl

theorem cell23_5496162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5496162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496162 prefixEnd_5496162 := by exact prefixLift 5496162
  have htrace : WordTrace (prefixWord ++ tailWord_5496162) baseStart_5496162 baseEnd_5496162 := by
    simpa [prefixWord, tailWord_5496162, baseEnd_5496162] using wordTrace_append hprefix tailTrace_5496162
  have hstable : (prefixWord ++ tailWord_5496162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496162).length < 2 ^ (prefixWord ++ tailWord_5496162).sum := by decide
  have hdescent : baseEnd_5496162 < baseStart_5496162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496172 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_5496172 : Nat := 118140960795 + 5496172 * 2 ^ 59
def prefixEnd_5496172 : Nat := 4983230072969 + 3 ^ 40 * 5496172 * 2
def baseEnd_5496172 : Nat := 2822177995783175435473571

theorem tailTrace_5496172 : CollatzResearch.WordTrace tailWord_5496172 prefixEnd_5496172 2822177995783175435473571 := by
  unfold tailWord_5496172
  simp only [CollatzResearch.WordTrace]
  refine ⟨100230930722157495145629385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133641240962876660194172513 100230930722157495145629385)
  ·
    refine ⟨75173198041618121359222039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100230930722157495145629385 75173198041618121359222039)
    ·
      refine ⟨112759797062427182038833059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75173198041618121359222039 112759797062427182038833059)
      ·
        refine ⟨169139695593640773058249589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112759797062427182038833059 169139695593640773058249589)
        ·
          refine ⟨15856846461903822474210899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169139695593640773058249589 15856846461903822474210899)
          ·
            refine ⟨23785269692855733711316349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15856846461903822474210899 23785269692855733711316349)
            ·
              refine ⟨8919476134820900141743631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23785269692855733711316349 8919476134820900141743631)
              ·
                refine ⟨13379214202231350212615447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919476134820900141743631 13379214202231350212615447)
                ·
                  refine ⟨20068821303347025318923171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13379214202231350212615447 20068821303347025318923171)
                  ·
                    refine ⟨30103231955020537978384757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20068821303347025318923171 30103231955020537978384757)
                    ·
                      refine ⟨2822177995783175435473571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30103231955020537978384757 2822177995783175435473571)
                      ·
                        rfl

theorem cell23_5496172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_5496172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496172 prefixEnd_5496172 := by exact prefixLift 5496172
  have htrace : WordTrace (prefixWord ++ tailWord_5496172) baseStart_5496172 baseEnd_5496172 := by
    simpa [prefixWord, tailWord_5496172, baseEnd_5496172] using wordTrace_append hprefix tailTrace_5496172
  have hstable : (prefixWord ++ tailWord_5496172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496172).length < 2 ^ (prefixWord ++ tailWord_5496172).sum := by decide
  have hdescent : baseEnd_5496172 < baseStart_5496172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496186 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2]
def baseStart_5496186 : Nat := 118140960795 + 5496186 * 2 ^ 59
def prefixEnd_5496186 : Nat := 4983230072969 + 3 ^ 40 * 5496186 * 2
def baseEnd_5496186 : Nat := 2822185184512338380698507

theorem tailTrace_5496186 : CollatzResearch.WordTrace tailWord_5496186 prefixEnd_5496186 2822185184512338380698507 := by
  unfold tailWord_5496186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50115593016566067670567103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133641581377509513788178941 50115593016566067670567103)
  ·
    refine ⟨75173389524849101505850655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50115593016566067670567103 75173389524849101505850655)
    ·
      refine ⟨112760084287273652258775983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75173389524849101505850655 112760084287273652258775983)
      ·
        refine ⟨169140126430910478388163975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112760084287273652258775983 169140126430910478388163975)
        ·
          refine ⟨253710189646365717582245963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169140126430910478388163975 253710189646365717582245963)
          ·
            refine ⟨380565284469548576373368945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253710189646365717582245963 380565284469548576373368945)
            ·
              refine ⟨285423963352161432280026709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380565284469548576373368945 285423963352161432280026709)
              ·
                refine ⟨3344812070533141784531563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 285423963352161432280026709 3344812070533141784531563)
                ·
                  refine ⟨5017218105799712676797345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344812070533141784531563 5017218105799712676797345)
                  ·
                    refine ⟨3762913579349784507598009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5017218105799712676797345 3762913579349784507598009)
                    ·
                      refine ⟨2822185184512338380698507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762913579349784507598009 2822185184512338380698507)
                      ·
                        rfl

theorem cell23_5496186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_5496186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496186 prefixEnd_5496186 := by exact prefixLift 5496186
  have htrace : WordTrace (prefixWord ++ tailWord_5496186) baseStart_5496186 baseEnd_5496186 := by
    simpa [prefixWord, tailWord_5496186, baseEnd_5496186] using wordTrace_append hprefix tailTrace_5496186
  have hstable : (prefixWord ++ tailWord_5496186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496186).length < 2 ^ (prefixWord ++ tailWord_5496186).sum := by decide
  have hdescent : baseEnd_5496186 < baseStart_5496186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496215 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_5496215 : Nat := 118140960795 + 5496215 * 2 ^ 59
def prefixEnd_5496215 : Nat := 4983230072969 + 3 ^ 40 * 5496215 * 2
def baseEnd_5496215 : Nat := 2822200075451318767235873

theorem tailTrace_5496215 : CollatzResearch.WordTrace tailWord_5496215 prefixEnd_5496215 2822200075451318767235873 := by
  unfold tailWord_5496215
  simp only [CollatzResearch.WordTrace]
  refine ⟨200463429783159208635074099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133642286522106139090049399 200463429783159208635074099)
  ·
    refine ⟨300695144674738812952611149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200463429783159208635074099 300695144674738812952611149)
    ·
      refine ⟨112760679253027054857229181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300695144674738812952611149 112760679253027054857229181)
      ·
        refine ⟨42285254719885145571460943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112760679253027054857229181 42285254719885145571460943)
        ·
          refine ⟨63427882079827718357191415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42285254719885145571460943 63427882079827718357191415)
          ·
            refine ⟨95141823119741577535787123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63427882079827718357191415 95141823119741577535787123)
            ·
              refine ⟨142712734679612366303680685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95141823119741577535787123 142712734679612366303680685)
              ·
                refine ⟨53517275504854637363880257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142712734679612366303680685 53517275504854637363880257)
                ·
                  refine ⟨40137956628640978022910193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53517275504854637363880257 40137956628640978022910193)
                  ·
                    refine ⟨30103467471480733517182645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40137956628640978022910193 30103467471480733517182645)
                    ·
                      refine ⟨2822200075451318767235873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30103467471480733517182645 2822200075451318767235873)
                      ·
                        rfl

theorem cell23_5496215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_5496215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496215 prefixEnd_5496215 := by exact prefixLift 5496215
  have htrace : WordTrace (prefixWord ++ tailWord_5496215) baseStart_5496215 baseEnd_5496215 := by
    simpa [prefixWord, tailWord_5496215, baseEnd_5496215] using wordTrace_append hprefix tailTrace_5496215
  have hstable : (prefixWord ++ tailWord_5496215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496215).length < 2 ^ (prefixWord ++ tailWord_5496215).sum := by decide
  have hdescent : baseEnd_5496215 < baseStart_5496215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496220 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5496220 : Nat := 118140960795 + 5496220 * 2 ^ 59
def prefixEnd_5496220 : Nat := 4983230072969 + 3 ^ 40 * 5496220 * 2
def baseEnd_5496220 : Nat := 2822202642854591247673351

theorem tailTrace_5496220 : CollatzResearch.WordTrace tailWord_5496220 prefixEnd_5496220 2822202642854591247673351 := by
  unfold tailWord_5496220
  simp only [CollatzResearch.WordTrace]
  refine ⟨100231806074070547244503057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133642408098760729659337409 100231806074070547244503057)
  ·
    refine ⟨75173854555552910433377293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100231806074070547244503057 75173854555552910433377293)
    ·
      refine ⟨28190195458332341412516485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75173854555552910433377293 28190195458332341412516485)
      ·
        refine ⟨5285661648437314014846841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28190195458332341412516485 5285661648437314014846841)
        ·
          refine ⟨3964246236327985511135131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5285661648437314014846841 3964246236327985511135131)
          ·
            refine ⟨5946369354491978266702697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964246236327985511135131 5946369354491978266702697)
            ·
              refine ⟨4459777015868983700027023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5946369354491978266702697 4459777015868983700027023)
              ·
                refine ⟨6689665523803475550040535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4459777015868983700027023 6689665523803475550040535)
                ·
                  refine ⟨10034498285705213325060803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6689665523803475550040535 10034498285705213325060803)
                  ·
                    refine ⟨15051747428557819987591205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10034498285705213325060803 15051747428557819987591205)
                    ·
                      refine ⟨2822202642854591247673351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15051747428557819987591205 2822202642854591247673351)
                      ·
                        rfl

theorem cell23_5496220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5496220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496220 prefixEnd_5496220 := by exact prefixLift 5496220
  have htrace : WordTrace (prefixWord ++ tailWord_5496220) baseStart_5496220 baseEnd_5496220 := by
    simpa [prefixWord, tailWord_5496220, baseEnd_5496220] using wordTrace_append hprefix tailTrace_5496220
  have hstable : (prefixWord ++ tailWord_5496220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496220).length < 2 ^ (prefixWord ++ tailWord_5496220).sum := by decide
  have hdescent : baseEnd_5496220 < baseStart_5496220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496259 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 1, 4, 2]
def baseStart_5496259 : Nat := 118140960795 + 5496259 * 2 ^ 59
def prefixEnd_5496259 : Nat := 4983230072969 + 3 ^ 40 * 5496259 * 2
def baseEnd_5496259 : Nat := 2822222668600116595085671

theorem tailTrace_5496259 : CollatzResearch.WordTrace tailWord_5496259 prefixEnd_5496259 2822222668600116595085671 := by
  unfold tailWord_5496259
  simp only [CollatzResearch.WordTrace]
  refine ⟨200465034594999804149675831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133643356396666536099783887 200465034594999804149675831)
  ·
    refine ⟨300697551892499706224513747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200465034594999804149675831 300697551892499706224513747)
    ·
      refine ⟨451046327838749559336770621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300697551892499706224513747 451046327838749559336770621)
      ·
        refine ⟨169142372939531084751288983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451046327838749559336770621 169142372939531084751288983)
        ·
          refine ⟨253713559409296627126933475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169142372939531084751288983 253713559409296627126933475)
          ·
            refine ⟨380570339113944940690400213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253713559409296627126933475 380570339113944940690400213)
            ·
              refine ⟨8919617322983084547431255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 380570339113944940690400213 8919617322983084547431255)
              ·
                refine ⟨13379425984474626821146883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919617322983084547431255 13379425984474626821146883)
                ·
                  refine ⟨20069138976711940231720325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13379425984474626821146883 20069138976711940231720325)
                  ·
                    refine ⟨3762963558133488793447561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20069138976711940231720325 3762963558133488793447561)
                    ·
                      refine ⟨2822222668600116595085671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762963558133488793447561 2822222668600116595085671)
                      ·
                        rfl

theorem cell23_5496259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_5496259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496259 prefixEnd_5496259 := by exact prefixLift 5496259
  have htrace : WordTrace (prefixWord ++ tailWord_5496259) baseStart_5496259 baseEnd_5496259 := by
    simpa [prefixWord, tailWord_5496259, baseEnd_5496259] using wordTrace_append hprefix tailTrace_5496259
  have hstable : (prefixWord ++ tailWord_5496259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496259).length < 2 ^ (prefixWord ++ tailWord_5496259).sum := by decide
  have hdescent : baseEnd_5496259 < baseStart_5496259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496292 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_5496292 : Nat := 118140960795 + 5496292 * 2 ^ 59
def prefixEnd_5496292 : Nat := 4983230072969 + 3 ^ 40 * 5496292 * 2
def baseEnd_5496292 : Nat := 2822239613461714965973019

theorem tailTrace_5496292 : CollatzResearch.WordTrace tailWord_5496292 prefixEnd_5496292 2822239613461714965973019 := by
  unfold tailWord_5496292
  simp only [CollatzResearch.WordTrace]
  refine ⟨100233119101940125392813565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133644158802586833857084753 100233119101940125392813565)
  ·
    refine ⟨37587419663227547022305087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100233119101940125392813565 37587419663227547022305087)
    ·
      refine ⟨56381129494841320533457631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37587419663227547022305087 56381129494841320533457631)
      ·
        refine ⟨84571694242261980800186447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56381129494841320533457631 84571694242261980800186447)
        ·
          refine ⟨126857541363392971200279671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84571694242261980800186447 126857541363392971200279671)
          ·
            refine ⟨190286312045089456800419507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126857541363392971200279671 190286312045089456800419507)
            ·
              refine ⟨285429468067634185200629261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190286312045089456800419507 285429468067634185200629261)
              ·
                refine ⟨107036050525362819450235973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285429468067634185200629261 107036050525362819450235973)
                ·
                  refine ⟨20069259473505528646919245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107036050525362819450235973 20069259473505528646919245)
                  ·
                    refine ⟨7525972302564573242594717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20069259473505528646919245 7525972302564573242594717)
                    ·
                      refine ⟨2822239613461714965973019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7525972302564573242594717 2822239613461714965973019)
                      ·
                        rfl

theorem cell23_5496292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_5496292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496292 prefixEnd_5496292 := by exact prefixLift 5496292
  have htrace : WordTrace (prefixWord ++ tailWord_5496292) baseStart_5496292 baseEnd_5496292 := by
    simpa [prefixWord, tailWord_5496292, baseEnd_5496292] using wordTrace_append hprefix tailTrace_5496292
  have hstable : (prefixWord ++ tailWord_5496292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496292).length < 2 ^ (prefixWord ++ tailWord_5496292).sum := by decide
  have hdescent : baseEnd_5496292 < baseStart_5496292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496310 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5496310 : Nat := 118140960795 + 5496310 * 2 ^ 59
def prefixEnd_5496310 : Nat := 4983230072969 + 3 ^ 40 * 5496310 * 2
def baseEnd_5496310 : Nat := 2822248856113495895547937

theorem tailTrace_5496310 : CollatzResearch.WordTrace tailWord_5496310 prefixEnd_5496310 2822248856113495895547937 := by
  unfold tailWord_5496310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12529180919863439991236399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133644596478543359906521589 12529180919863439991236399)
  ·
    refine ⟨18793771379795159986854599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12529180919863439991236399 18793771379795159986854599)
    ·
      refine ⟨28190657069692739980281899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18793771379795159986854599 28190657069692739980281899)
      ·
        refine ⟨42285985604539109970422849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28190657069692739980281899 42285985604539109970422849)
        ·
          refine ⟨31714489203404332477817137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42285985604539109970422849 31714489203404332477817137)
          ·
            refine ⟨23785866902553249358362853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31714489203404332477817137 23785866902553249358362853)
            ·
              refine ⟨4459850044228734254693035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23785866902553249358362853 4459850044228734254693035)
              ·
                refine ⟨6689775066343101382039553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4459850044228734254693035 6689775066343101382039553)
                ·
                  refine ⟨5017331299757326036529665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6689775066343101382039553 5017331299757326036529665)
                  ·
                    refine ⟨3762998474817994527397249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5017331299757326036529665 3762998474817994527397249)
                    ·
                      refine ⟨2822248856113495895547937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3762998474817994527397249 2822248856113495895547937)
                      ·
                        rfl

theorem cell23_5496310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5496310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496310 prefixEnd_5496310 := by exact prefixLift 5496310
  have htrace : WordTrace (prefixWord ++ tailWord_5496310) baseStart_5496310 baseEnd_5496310 := by
    simpa [prefixWord, tailWord_5496310, baseEnd_5496310] using wordTrace_append hprefix tailTrace_5496310
  have hstable : (prefixWord ++ tailWord_5496310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496310).length < 2 ^ (prefixWord ++ tailWord_5496310).sum := by decide
  have hdescent : baseEnd_5496310 < baseStart_5496310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496349 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5496349 : Nat := 118140960795 + 5496349 * 2 ^ 59
def prefixEnd_5496349 : Nat := 4983230072969 + 3 ^ 40 * 5496349 * 2
def baseEnd_5496349 : Nat := 2822268881859021242960257

theorem tailTrace_5496349 : CollatzResearch.WordTrace tailWord_5496349 prefixEnd_5496349 2822268881859021242960257 := by
  unfold tailWord_5496349
  simp only [CollatzResearch.WordTrace]
  refine ⟨200468317164673749520452101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133645544776449166346968067 200468317164673749520452101)
  ·
    refine ⟨37587809468376328035084769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200468317164673749520452101 37587809468376328035084769)
    ·
      refine ⟨28190857101282246026313577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37587809468376328035084769 28190857101282246026313577)
      ·
        refine ⟨21143142825961684519735183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28190857101282246026313577 21143142825961684519735183)
        ·
          refine ⟨31714714238942526779602775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21143142825961684519735183 31714714238942526779602775)
          ·
            refine ⟨47572071358413790169404163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31714714238942526779602775 47572071358413790169404163)
            ·
              refine ⟨71358107037620685254106245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47572071358413790169404163 71358107037620685254106245)
              ·
                refine ⟨13379645069553878485144921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71358107037620685254106245 13379645069553878485144921)
                ·
                  refine ⟨10034733802165408863858691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13379645069553878485144921 10034733802165408863858691)
                  ·
                    refine ⟨15052100703248113295788037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10034733802165408863858691 15052100703248113295788037)
                    ·
                      refine ⟨2822268881859021242960257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15052100703248113295788037 2822268881859021242960257)
                      ·
                        rfl

theorem cell23_5496349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5496349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496349 prefixEnd_5496349 := by exact prefixLift 5496349
  have htrace : WordTrace (prefixWord ++ tailWord_5496349) baseStart_5496349 baseEnd_5496349 := by
    simpa [prefixWord, tailWord_5496349, baseEnd_5496349] using wordTrace_append hprefix tailTrace_5496349
  have hstable : (prefixWord ++ tailWord_5496349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496349).length < 2 ^ (prefixWord ++ tailWord_5496349).sum := by decide
  have hdescent : baseEnd_5496349 < baseStart_5496349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496366 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_5496366 : Nat := 118140960795 + 5496366 * 2 ^ 59
def prefixEnd_5496366 : Nat := 4983230072969 + 3 ^ 40 * 5496366 * 2
def baseEnd_5496366 : Nat := 2822277611030147676447679

theorem tailTrace_5496366 : CollatzResearch.WordTrace tailWord_5496366 prefixEnd_5496366 2822277611030147676447679 := by
  unfold tailWord_5496366
  simp only [CollatzResearch.WordTrace]
  refine ⟨25058617150701520177977619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133645958137074774282547301 25058617150701520177977619)
  ·
    refine ⟨37587925726052280266966429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25058617150701520177977619 37587925726052280266966429)
    ·
      refine ⟨14095472147269605100112411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37587925726052280266966429 14095472147269605100112411)
      ·
        refine ⟨21143208220904407650168617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14095472147269605100112411 21143208220904407650168617)
        ·
          refine ⟨15857406165678305737626463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21143208220904407650168617 15857406165678305737626463)
          ·
            refine ⟨23786109248517458606439695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15857406165678305737626463 23786109248517458606439695)
            ·
              refine ⟨35679163872776187909659543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23786109248517458606439695 35679163872776187909659543)
              ·
                refine ⟨53518745809164281864489315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35679163872776187909659543 53518745809164281864489315)
                ·
                  refine ⟨80278118713746422796733973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53518745809164281864489315 80278118713746422796733973)
                  ·
                    refine ⟨3763036814706863568596905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80278118713746422796733973 3763036814706863568596905)
                    ·
                      refine ⟨2822277611030147676447679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763036814706863568596905 2822277611030147676447679)
                      ·
                        rfl

theorem cell23_5496366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_5496366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496366 prefixEnd_5496366 := by exact prefixLift 5496366
  have htrace : WordTrace (prefixWord ++ tailWord_5496366) baseStart_5496366 baseEnd_5496366 := by
    simpa [prefixWord, tailWord_5496366, baseEnd_5496366] using wordTrace_append hprefix tailTrace_5496366
  have hstable : (prefixWord ++ tailWord_5496366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496366).length < 2 ^ (prefixWord ++ tailWord_5496366).sum := by decide
  have hdescent : baseEnd_5496366 < baseStart_5496366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496399 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 3]
def baseStart_5496399 : Nat := 118140960795 + 5496399 * 2 ^ 59
def prefixEnd_5496399 : Nat := 4983230072969 + 3 ^ 40 * 5496399 * 2
def baseEnd_5496399 : Nat := 2822294555891746047335027

theorem tailTrace_5496399 : CollatzResearch.WordTrace tailWord_5496399 prefixEnd_5496399 2822294555891746047335027 := by
  unfold tailWord_5496399
  simp only [CollatzResearch.WordTrace]
  refine ⟨200470140814492608059772251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133646760542995072039848167 200470140814492608059772251)
  ·
    refine ⟨300705211221738912089658377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200470140814492608059772251 300705211221738912089658377)
    ·
      refine ⟨225528908416304184067243783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300705211221738912089658377 225528908416304184067243783)
      ·
        refine ⟨338293362624456276100865675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225528908416304184067243783 338293362624456276100865675)
        ·
          refine ⟨507440043936684414151298513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338293362624456276100865675 507440043936684414151298513)
          ·
            refine ⟨380580032952513310613473885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507440043936684414151298513 380580032952513310613473885)
            ·
              refine ⟨142717512357192491480052707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380580032952513310613473885 142717512357192491480052707)
              ·
                refine ⟨214076268535788737220079061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142717512357192491480052707 214076268535788737220079061)
                ·
                  refine ⟨5017412543807548528595603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 214076268535788737220079061 5017412543807548528595603)
                  ·
                    refine ⟨7526118815711322792893405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017412543807548528595603 7526118815711322792893405)
                    ·
                      refine ⟨2822294555891746047335027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526118815711322792893405 2822294555891746047335027)
                      ·
                        rfl

theorem cell23_5496399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_5496399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496399 prefixEnd_5496399 := by exact prefixLift 5496399
  have htrace : WordTrace (prefixWord ++ tailWord_5496399) baseStart_5496399 baseEnd_5496399 := by
    simpa [prefixWord, tailWord_5496399, baseEnd_5496399] using wordTrace_append hprefix tailTrace_5496399
  have hstable : (prefixWord ++ tailWord_5496399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496399).length < 2 ^ (prefixWord ++ tailWord_5496399).sum := by decide
  have hdescent : baseEnd_5496399 < baseStart_5496399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496426 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_5496426 : Nat := 118140960795 + 5496426 * 2 ^ 59
def prefixEnd_5496426 : Nat := 4983230072969 + 3 ^ 40 * 5496426 * 2
def baseEnd_5496426 : Nat := 2822308419869417441697403

theorem tailTrace_5496426 : CollatzResearch.WordTrace tailWord_5496426 prefixEnd_5496426 2822308419869417441697403 := by
  unfold tailWord_5496426
  simp only [CollatzResearch.WordTrace]
  refine ⟨50117781396348697917751283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133647417056929861114003421 50117781396348697917751283)
  ·
    refine ⟨75176672094523046876626925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50117781396348697917751283 75176672094523046876626925)
    ·
      refine ⟨28191252035446142578735097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75176672094523046876626925 28191252035446142578735097)
      ·
        refine ⟨21143439026584606934051323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28191252035446142578735097 21143439026584606934051323)
        ·
          refine ⟨31715158539876910401076985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21143439026584606934051323 31715158539876910401076985)
          ·
            refine ⟨23786368904907682800807739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31715158539876910401076985 23786368904907682800807739)
            ·
              refine ⟨35679553357361524201211609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23786368904907682800807739 35679553357361524201211609)
              ·
                refine ⟨26759665018021143150908707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35679553357361524201211609 26759665018021143150908707)
                ·
                  refine ⟨40139497527031714726363061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26759665018021143150908707 40139497527031714726363061)
                  ·
                    refine ⟨3763077893159223255596537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40139497527031714726363061 3763077893159223255596537)
                    ·
                      refine ⟨2822308419869417441697403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763077893159223255596537 2822308419869417441697403)
                      ·
                        rfl

theorem cell23_5496426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_5496426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496426 prefixEnd_5496426 := by exact prefixLift 5496426
  have htrace : WordTrace (prefixWord ++ tailWord_5496426) baseStart_5496426 baseEnd_5496426 := by
    simpa [prefixWord, tailWord_5496426, baseEnd_5496426] using wordTrace_append hprefix tailTrace_5496426
  have hstable : (prefixWord ++ tailWord_5496426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496426).length < 2 ^ (prefixWord ++ tailWord_5496426).sum := by decide
  have hdescent : baseEnd_5496426 < baseStart_5496426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496439 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 8, 2]
def baseStart_5496439 : Nat := 118140960795 + 5496439 * 2 ^ 59
def prefixEnd_5496439 : Nat := 4983230072969 + 3 ^ 40 * 5496439 * 2
def baseEnd_5496439 : Nat := 2822315095117925890834843

theorem tailTrace_5496439 : CollatzResearch.WordTrace tailWord_5496439 prefixEnd_5496439 2822315095117925890834843 := by
  unfold tailWord_5496439
  simp only [CollatzResearch.WordTrace]
  refine ⟨200471599734347694891228371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133647733156231796594152247 200471599734347694891228371)
  ·
    refine ⟨300707399601521542336842557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200471599734347694891228371 300707399601521542336842557)
    ·
      refine ⟨112765274850570578376315959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300707399601521542336842557 112765274850570578376315959)
      ·
        refine ⟨169147912275855867564473939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112765274850570578376315959 169147912275855867564473939)
        ·
          refine ⟨253721868413783801346710909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169147912275855867564473939 253721868413783801346710909)
          ·
            refine ⟨95145700655168925505016591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253721868413783801346710909 95145700655168925505016591)
            ·
              refine ⟨142718550982753388257524887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95145700655168925505016591 142718550982753388257524887)
              ·
                refine ⟨214077826474130082386287331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142718550982753388257524887 214077826474130082386287331)
                ·
                  refine ⟨321116739711195123579430997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214077826474130082386287331 321116739711195123579430997)
                  ·
                    refine ⟨3763086793490567854446457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 321116739711195123579430997 3763086793490567854446457)
                    ·
                      refine ⟨2822315095117925890834843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763086793490567854446457 2822315095117925890834843)
                      ·
                        rfl

theorem cell23_5496439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_5496439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496439 prefixEnd_5496439 := by exact prefixLift 5496439
  have htrace : WordTrace (prefixWord ++ tailWord_5496439) baseStart_5496439 baseEnd_5496439 := by
    simpa [prefixWord, tailWord_5496439, baseEnd_5496439] using wordTrace_append hprefix tailTrace_5496439
  have hstable : (prefixWord ++ tailWord_5496439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496439).length < 2 ^ (prefixWord ++ tailWord_5496439).sum := by decide
  have hdescent : baseEnd_5496439 < baseStart_5496439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496459 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 5]
def baseStart_5496459 : Nat := 118140960795 + 5496459 * 2 ^ 59
def prefixEnd_5496459 : Nat := 4983230072969 + 3 ^ 40 * 5496459 * 2
def baseEnd_5496459 : Nat := 2822325364731015812584751

theorem tailTrace_5496459 : CollatzResearch.WordTrace tailWord_5496459 prefixEnd_5496459 2822325364731015812584751 := by
  unfold tailWord_5496459
  simp only [CollatzResearch.WordTrace]
  refine ⟨200472329194275238306956431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133648219462850158871304287 200472329194275238306956431)
  ·
    refine ⟨300708493791412857460434647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200472329194275238306956431 300708493791412857460434647)
    ·
      refine ⟨451062740687119286190651971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300708493791412857460434647 451062740687119286190651971)
      ·
        refine ⟨676594111030678929285977957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451062740687119286190651971 676594111030678929285977957)
        ·
          refine ⟨126861395818252299241120867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 676594111030678929285977957 126861395818252299241120867)
          ·
            refine ⟨190292093727378448861681301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126861395818252299241120867 190292093727378448861681301)
            ·
              refine ⟨8919941893470864790391311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190292093727378448861681301 8919941893470864790391311)
              ·
                refine ⟨13379912840206297185586967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8919941893470864790391311 13379912840206297185586967)
                ·
                  refine ⟨20069869260309445778380451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13379912840206297185586967 20069869260309445778380451)
                  ·
                    refine ⟨30104803890464168667570677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20069869260309445778380451 30104803890464168667570677)
                    ·
                      refine ⟨2822325364731015812584751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30104803890464168667570677 2822325364731015812584751)
                      ·
                        rfl

theorem cell23_5496459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 5].length) (baseStart_5496459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496459 prefixEnd_5496459 := by exact prefixLift 5496459
  have htrace : WordTrace (prefixWord ++ tailWord_5496459) baseStart_5496459 baseEnd_5496459 := by
    simpa [prefixWord, tailWord_5496459, baseEnd_5496459] using wordTrace_append hprefix tailTrace_5496459
  have hstable : (prefixWord ++ tailWord_5496459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496459).length < 2 ^ (prefixWord ++ tailWord_5496459).sum := by decide
  have hdescent : baseEnd_5496459 < baseStart_5496459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496506 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_5496506 : Nat := 118140960795 + 5496506 * 2 ^ 59
def prefixEnd_5496506 : Nat := 4983230072969 + 3 ^ 40 * 5496506 * 2
def baseEnd_5496506 : Nat := 2822349498321777128697035

theorem tailTrace_5496506 : CollatzResearch.WordTrace tailWord_5496506 prefixEnd_5496506 2822349498321777128697035 := by
  unfold tailWord_5496506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50118510856276241333479343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133649362283403310222611581 50118510856276241333479343)
  ·
    refine ⟨75177766284414362000219015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50118510856276241333479343 75177766284414362000219015)
    ·
      refine ⟨112766649426621543000328523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75177766284414362000219015 112766649426621543000328523)
      ·
        refine ⟨169149974139932314500492785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112766649426621543000328523 169149974139932314500492785)
        ·
          refine ⟨126862480604949235875369589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169149974139932314500492785 126862480604949235875369589)
          ·
            refine ⟨11893357556713990863315899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126862480604949235875369589 11893357556713990863315899)
            ·
              refine ⟨17840036335070986294973849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11893357556713990863315899 17840036335070986294973849)
              ·
                refine ⟨13380027251303239721230387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17840036335070986294973849 13380027251303239721230387)
                ·
                  refine ⟨20070040876954859581845581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13380027251303239721230387 20070040876954859581845581)
                  ·
                    refine ⟨7526265328858072343192093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20070040876954859581845581 7526265328858072343192093)
                    ·
                      refine ⟨2822349498321777128697035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526265328858072343192093 2822349498321777128697035)
                      ·
                        rfl

theorem cell23_5496506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_5496506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496506 prefixEnd_5496506 := by exact prefixLift 5496506
  have htrace : WordTrace (prefixWord ++ tailWord_5496506) baseStart_5496506 baseEnd_5496506 := by
    simpa [prefixWord, tailWord_5496506, baseEnd_5496506] using wordTrace_append hprefix tailTrace_5496506
  have hstable : (prefixWord ++ tailWord_5496506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496506).length < 2 ^ (prefixWord ++ tailWord_5496506).sum := by decide
  have hdescent : baseEnd_5496506 < baseStart_5496506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496510 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_5496510 : Nat := 118140960795 + 5496510 * 2 ^ 59
def prefixEnd_5496510 : Nat := 4983230072969 + 3 ^ 40 * 5496510 * 2
def baseEnd_5496510 : Nat := 2822351552244395113047017

theorem tailTrace_5496510 : CollatzResearch.WordTrace tailWord_5496510 prefixEnd_5496510 2822351552244395113047017 := by
  unfold tailWord_5496510
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059273664636309252132873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133649459544726982678041989 25059273664636309252132873)
  ·
    refine ⟨18794455248477231939099655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25059273664636309252132873 18794455248477231939099655)
    ·
      refine ⟨28191682872715847908649483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18794455248477231939099655 28191682872715847908649483)
      ·
        refine ⟨42287524309073771862974225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28191682872715847908649483 42287524309073771862974225)
        ·
          refine ⟨31715643231805328897230669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42287524309073771862974225 31715643231805328897230669)
          ·
            refine ⟨11893366211926998336461501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31715643231805328897230669 11893366211926998336461501)
            ·
              refine ⟨4460012329472624376173063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11893366211926998336461501 4460012329472624376173063)
              ·
                refine ⟨6690018494208936564259595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460012329472624376173063 6690018494208936564259595)
                ·
                  refine ⟨10035027741313404846389393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690018494208936564259595 10035027741313404846389393)
                  ·
                    refine ⟨7526270805985053634792045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10035027741313404846389393 7526270805985053634792045)
                    ·
                      refine ⟨2822351552244395113047017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526270805985053634792045 2822351552244395113047017)
                      ·
                        rfl

theorem cell23_5496510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_5496510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496510 prefixEnd_5496510 := by exact prefixLift 5496510
  have htrace : WordTrace (prefixWord ++ tailWord_5496510) baseStart_5496510 baseEnd_5496510 := by
    simpa [prefixWord, tailWord_5496510, baseEnd_5496510] using wordTrace_append hprefix tailTrace_5496510
  have hstable : (prefixWord ++ tailWord_5496510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496510).length < 2 ^ (prefixWord ++ tailWord_5496510).sum := by decide
  have hdescent : baseEnd_5496510 < baseStart_5496510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496529 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_5496529 : Nat := 118140960795 + 5496529 * 2 ^ 59
def prefixEnd_5496529 : Nat := 4983230072969 + 3 ^ 40 * 5496529 * 2
def baseEnd_5496529 : Nat := 2822361308376830538709429

theorem tailTrace_5496529 : CollatzResearch.WordTrace tailWord_5496529 prefixEnd_5496529 2822361308376830538709429 := by
  unfold tailWord_5496529
  simp only [CollatzResearch.WordTrace]
  refine ⟨200474882304021640262004641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133649921536014426841336427 200474882304021640262004641)
  ·
    refine ⟨150356161728016230196503481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200474882304021640262004641 150356161728016230196503481)
    ·
      refine ⟨112767121296012172647377611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150356161728016230196503481 112767121296012172647377611)
      ·
        refine ⟨169150681944018258971066417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112767121296012172647377611 169150681944018258971066417)
        ·
          refine ⟨126863011458013694228299813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169150681944018258971066417 126863011458013694228299813)
          ·
            refine ⟨23786814648377567667806215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126863011458013694228299813 23786814648377567667806215)
            ·
              refine ⟨35680221972566351501709323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23786814648377567667806215 35680221972566351501709323)
              ·
                refine ⟨53520332958849527252563985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35680221972566351501709323 53520332958849527252563985)
                ·
                  refine ⟨40140249719137145439422989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53520332958849527252563985 40140249719137145439422989)
                  ·
                    refine ⟨15052593644676429539783621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40140249719137145439422989 15052593644676429539783621)
                    ·
                      refine ⟨2822361308376830538709429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15052593644676429539783621 2822361308376830538709429)
                      ·
                        rfl

theorem cell23_5496529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_5496529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496529 prefixEnd_5496529 := by exact prefixLift 5496529
  have htrace : WordTrace (prefixWord ++ tailWord_5496529) baseStart_5496529 baseEnd_5496529 := by
    simpa [prefixWord, tailWord_5496529, baseEnd_5496529] using wordTrace_append hprefix tailTrace_5496529
  have hstable : (prefixWord ++ tailWord_5496529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496529).length < 2 ^ (prefixWord ++ tailWord_5496529).sum := by decide
  have hdescent : baseEnd_5496529 < baseStart_5496529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496540 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5496540 : Nat := 118140960795 + 5496540 * 2 ^ 59
def prefixEnd_5496540 : Nat := 4983230072969 + 3 ^ 40 * 5496540 * 2
def baseEnd_5496540 : Nat := 2822366956664029995671879

theorem tailTrace_5496540 : CollatzResearch.WordTrace tailWord_5496540 prefixEnd_5496540 2822366956664029995671879 := by
  unfold tailWord_5496540
  simp only [CollatzResearch.WordTrace]
  refine ⟨100237641753490894570327537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133650189004654526093770049 100237641753490894570327537)
  ·
    refine ⟨75178231315118170927745653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100237641753490894570327537 75178231315118170927745653)
    ·
      refine ⟨7047959185792328524476155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75178231315118170927745653 7047959185792328524476155)
      ·
        refine ⟨10571938778688492786714233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7047959185792328524476155 10571938778688492786714233)
        ·
          refine ⟨7928954084016369590035675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10571938778688492786714233 7928954084016369590035675)
          ·
            refine ⟨11893431126024554385053513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7928954084016369590035675 11893431126024554385053513)
            ·
              refine ⟨8920073344518415788790135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11893431126024554385053513 8920073344518415788790135)
              ·
                refine ⟨13380110016777623683185203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8920073344518415788790135 13380110016777623683185203)
                ·
                  refine ⟨20070165025166435524777805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13380110016777623683185203 20070165025166435524777805)
                  ·
                    refine ⟨7526311884437413321791677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20070165025166435524777805 7526311884437413321791677)
                    ·
                      refine ⟨2822366956664029995671879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526311884437413321791677 2822366956664029995671879)
                      ·
                        rfl

theorem cell23_5496540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5496540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496540 prefixEnd_5496540 := by exact prefixLift 5496540
  have htrace : WordTrace (prefixWord ++ tailWord_5496540) baseStart_5496540 baseEnd_5496540 := by
    simpa [prefixWord, tailWord_5496540, baseEnd_5496540] using wordTrace_append hprefix tailTrace_5496540
  have hstable : (prefixWord ++ tailWord_5496540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496540).length < 2 ^ (prefixWord ++ tailWord_5496540).sum := by decide
  have hdescent : baseEnd_5496540 < baseStart_5496540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496559 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_5496559 : Nat := 118140960795 + 5496559 * 2 ^ 59
def prefixEnd_5496559 : Nat := 4983230072969 + 3 ^ 40 * 5496559 * 2
def baseEnd_5496559 : Nat := 2822376712796465421334291

theorem tailTrace_5496559 : CollatzResearch.WordTrace tailWord_5496559 prefixEnd_5496559 2822376712796465421334291 := by
  unfold tailWord_5496559
  simp only [CollatzResearch.WordTrace]
  refine ⟨200475976493912955385596731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133650650995941970257064487 200475976493912955385596731)
  ·
    refine ⟨300713964740869433078395097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200475976493912955385596731 300713964740869433078395097)
    ·
      refine ⟨225535473555652074808796323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300713964740869433078395097 225535473555652074808796323)
      ·
        refine ⟨338303210333478112213194485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225535473555652074808796323 338303210333478112213194485)
        ·
          refine ⟨31715925968763573019986983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338303210333478112213194485 31715925968763573019986983)
          ·
            refine ⟨47573888953145359529980475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31715925968763573019986983 47573888953145359529980475)
            ·
              refine ⟨71360833429718039294970713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47573888953145359529980475 71360833429718039294970713)
              ·
                refine ⟨53520625072288529471228035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71360833429718039294970713 53520625072288529471228035)
                ·
                  refine ⟨80280937608432794206842053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53520625072288529471228035 80280937608432794206842053)
                  ·
                    refine ⟨15052675801581148913782885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80280937608432794206842053 15052675801581148913782885)
                    ·
                      refine ⟨2822376712796465421334291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15052675801581148913782885 2822376712796465421334291)
                      ·
                        rfl

theorem cell23_5496559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_5496559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496559 prefixEnd_5496559 := by exact prefixLift 5496559
  have htrace : WordTrace (prefixWord ++ tailWord_5496559) baseStart_5496559 baseEnd_5496559 := by
    simpa [prefixWord, tailWord_5496559, baseEnd_5496559] using wordTrace_append hprefix tailTrace_5496559
  have hstable : (prefixWord ++ tailWord_5496559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496559).length < 2 ^ (prefixWord ++ tailWord_5496559).sum := by decide
  have hdescent : baseEnd_5496559 < baseStart_5496559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496574 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_5496574 : Nat := 118140960795 + 5496574 * 2 ^ 59
def prefixEnd_5496574 : Nat := 4983230072969 + 3 ^ 40 * 5496574 * 2
def baseEnd_5496574 : Nat := 2822384415006282862646723

theorem tailTrace_5496574 : CollatzResearch.WordTrace tailWord_5496574 prefixEnd_5496574 2822384415006282862646723 := by
  unfold tailWord_5496574
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059565448607326618424097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133651015725905741964928517 25059565448607326618424097)
  ·
    refine ⟨18794674086455494963818073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25059565448607326618424097 18794674086455494963818073)
    ·
      refine ⟨14096005564841621222863555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18794674086455494963818073 14096005564841621222863555)
      ·
        refine ⟨21144008347262431834295333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14096005564841621222863555 21144008347262431834295333)
        ·
          refine ⟨3964501565111705968930375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21144008347262431834295333 3964501565111705968930375)
          ·
            refine ⟨5946752347667558953395563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964501565111705968930375 5946752347667558953395563)
            ·
              refine ⟨8920128521501338430093345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946752347667558953395563 8920128521501338430093345)
              ·
                refine ⟨6690096391126003822570009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8920128521501338430093345 6690096391126003822570009)
                ·
                  refine ⟨5017572293344502866927507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6690096391126003822570009 5017572293344502866927507)
                  ·
                    refine ⟨7526358440016754300391261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017572293344502866927507 7526358440016754300391261)
                    ·
                      refine ⟨2822384415006282862646723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526358440016754300391261 2822384415006282862646723)
                      ·
                        rfl

theorem cell23_5496574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_5496574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496574 prefixEnd_5496574 := by exact prefixLift 5496574
  have htrace : WordTrace (prefixWord ++ tailWord_5496574) baseStart_5496574 baseEnd_5496574 := by
    simpa [prefixWord, tailWord_5496574, baseEnd_5496574] using wordTrace_append hprefix tailTrace_5496574
  have hstable : (prefixWord ++ tailWord_5496574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496574).length < 2 ^ (prefixWord ++ tailWord_5496574).sum := by decide
  have hdescent : baseEnd_5496574 < baseStart_5496574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496580 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5496580 : Nat := 118140960795 + 5496580 * 2 ^ 59
def prefixEnd_5496580 : Nat := 4983230072969 + 3 ^ 40 * 5496580 * 2
def baseEnd_5496580 : Nat := 2822387495890209839171695

theorem tailTrace_5496580 : CollatzResearch.WordTrace tailWord_5496580 prefixEnd_5496580 2822387495890209839171695 := by
  unfold tailWord_5496580
  simp only [CollatzResearch.WordTrace]
  refine ⟨100238371213418437986055597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133651161617891250648074129 100238371213418437986055597)
  ·
    refine ⟨37589389205031914244770849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100238371213418437986055597 37589389205031914244770849)
    ·
      refine ⟨28192041903773935683578137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37589389205031914244770849 28192041903773935683578137)
      ·
        refine ⟨21144031427830451762683603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28192041903773935683578137 21144031427830451762683603)
        ·
          refine ⟨31716047141745677644025405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21144031427830451762683603 31716047141745677644025405)
          ·
            refine ⟨11893517678154629116509527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31716047141745677644025405 11893517678154629116509527)
            ·
              refine ⟨17840276517231943674764291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11893517678154629116509527 17840276517231943674764291)
              ·
                refine ⟨26760414775847915512146437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17840276517231943674764291 26760414775847915512146437)
                ·
                  refine ⟨5017577770471484158527457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26760414775847915512146437 5017577770471484158527457)
                  ·
                    refine ⟨3763183327853613118895593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5017577770471484158527457 3763183327853613118895593)
                    ·
                      refine ⟨2822387495890209839171695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763183327853613118895593 2822387495890209839171695)
                      ·
                        rfl

theorem cell23_5496580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5496580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496580 prefixEnd_5496580 := by exact prefixLift 5496580
  have htrace : WordTrace (prefixWord ++ tailWord_5496580) baseStart_5496580 baseEnd_5496580 := by
    simpa [prefixWord, tailWord_5496580, baseEnd_5496580] using wordTrace_append hprefix tailTrace_5496580
  have hstable : (prefixWord ++ tailWord_5496580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496580).length < 2 ^ (prefixWord ++ tailWord_5496580).sum := by decide
  have hdescent : baseEnd_5496580 < baseStart_5496580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496586 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_5496586 : Nat := 118140960795 + 5496586 * 2 ^ 59
def prefixEnd_5496586 : Nat := 4983230072969 + 3 ^ 40 * 5496586 * 2
def baseEnd_5496586 : Nat := 313598952974904090632963

theorem tailTrace_5496586 : CollatzResearch.WordTrace tailWord_5496586 prefixEnd_5496586 313598952974904090632963 := by
  unfold tailWord_5496586
  simp only [CollatzResearch.WordTrace]
  refine ⟨50119240316203784749207403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133651307509876759331219741 50119240316203784749207403)
  ·
    refine ⟨75178860474305677123811105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50119240316203784749207403 75178860474305677123811105)
    ·
      refine ⟨56384145355729257842858329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75178860474305677123811105 56384145355729257842858329)
      ·
        refine ⟨42288109016796943382143747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56384145355729257842858329 42288109016796943382143747)
        ·
          refine ⟨63432163525195415073215621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42288109016796943382143747 63432163525195415073215621)
          ·
            refine ⟨11893530660974140326227929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63432163525195415073215621 11893530660974140326227929)
            ·
              refine ⟨8920147995730605244670947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11893530660974140326227929 8920147995730605244670947)
              ·
                refine ⟨13380221993595907867006421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8920147995730605244670947 13380221993595907867006421)
                ·
                  refine ⟨313598952974904090632963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13380221993595907867006421 313598952974904090632963)
                  ·
                    rfl

theorem cell23_5496586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_5496586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496586 prefixEnd_5496586 := by exact prefixLift 5496586
  have htrace : WordTrace (prefixWord ++ tailWord_5496586) baseStart_5496586 baseEnd_5496586 := by
    simpa [prefixWord, tailWord_5496586, baseEnd_5496586] using wordTrace_append hprefix tailTrace_5496586
  have hstable : (prefixWord ++ tailWord_5496586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496586).length < 2 ^ (prefixWord ++ tailWord_5496586).sum := by decide
  have hdescent : baseEnd_5496586 < baseStart_5496586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496597 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_5496597 : Nat := 118140960795 + 5496597 * 2 ^ 59
def prefixEnd_5496597 : Nat := 4983230072969 + 3 ^ 40 * 5496597 * 2
def baseEnd_5496597 : Nat := 2822396225061336272659117

theorem tailTrace_5496597 : CollatzResearch.WordTrace tailWord_5496597 prefixEnd_5496597 2822396225061336272659117 := by
  unfold tailWord_5496597
  simp only [CollatzResearch.WordTrace]
  refine ⟨200477362467775287875480045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133651574978516858583653363 200477362467775287875480045)
  ·
    refine ⟨75179010925415732953305017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200477362467775287875480045 75179010925415732953305017)
    ·
      refine ⟨56384258194061799714978763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75179010925415732953305017 56384258194061799714978763)
      ·
        refine ⟨84576387291092699572468145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56384258194061799714978763 84576387291092699572468145)
        ·
          refine ⟨63432290468319524679351109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84576387291092699572468145 63432290468319524679351109)
          ·
            refine ⟨11893554462809910877378333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63432290468319524679351109 11893554462809910877378333)
            ·
              refine ⟨4460082923553716579016875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11893554462809910877378333 4460082923553716579016875)
              ·
                refine ⟨6690124385330574868525313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460082923553716579016875 6690124385330574868525313)
                ·
                  refine ⟨5017593288997931151393985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6690124385330574868525313 5017593288997931151393985)
                  ·
                    refine ⟨3763194966748448363545489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5017593288997931151393985 3763194966748448363545489)
                    ·
                      refine ⟨2822396225061336272659117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763194966748448363545489 2822396225061336272659117)
                      ·
                        rfl

theorem cell23_5496597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_5496597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496597 prefixEnd_5496597 := by exact prefixLift 5496597
  have htrace : WordTrace (prefixWord ++ tailWord_5496597) baseStart_5496597 baseEnd_5496597 := by
    simpa [prefixWord, tailWord_5496597, baseEnd_5496597] using wordTrace_append hprefix tailTrace_5496597
  have hstable : (prefixWord ++ tailWord_5496597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496597).length < 2 ^ (prefixWord ++ tailWord_5496597).sum := by decide
  have hdescent : baseEnd_5496597 < baseStart_5496597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496616 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5496616 : Nat := 118140960795 + 5496616 * 2 ^ 59
def prefixEnd_5496616 : Nat := 4983230072969 + 3 ^ 40 * 5496616 * 2
def baseEnd_5496616 : Nat := 940801993731257232773843

theorem tailTrace_5496616 : CollatzResearch.WordTrace tailWord_5496616 prefixEnd_5496616 940801993731257232773843 := by
  unfold tailWord_5496616
  simp only [CollatzResearch.WordTrace]
  refine ⟨100239027727353227060210851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133652036969804302746947801 100239027727353227060210851)
  ·
    refine ⟨150358541591029840590316277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100239027727353227060210851 150358541591029840590316277)
    ·
      refine ⟨14096113274159047555342151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150358541591029840590316277 14096113274159047555342151)
      ·
        refine ⟨21144169911238571333013227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14096113274159047555342151 21144169911238571333013227)
        ·
          refine ⟨31716254866857856999519841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21144169911238571333013227 31716254866857856999519841)
          ·
            refine ⟨23787191150143392749639881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31716254866857856999519841 23787191150143392749639881)
            ·
              refine ⟨17840393362607544562229911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23787191150143392749639881 17840393362607544562229911)
              ·
                refine ⟨26760590043911316843344867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17840393362607544562229911 26760590043911316843344867)
                ·
                  refine ⟨40140885065866975265017301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26760590043911316843344867 40140885065866975265017301)
                  ·
                    refine ⟨940801993731257232773843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40140885065866975265017301 940801993731257232773843)
                    ·
                      rfl

theorem cell23_5496616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5496616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496616 prefixEnd_5496616 := by exact prefixLift 5496616
  have htrace : WordTrace (prefixWord ++ tailWord_5496616) baseStart_5496616 baseEnd_5496616 := by
    simpa [prefixWord, tailWord_5496616, baseEnd_5496616] using wordTrace_append hprefix tailTrace_5496616
  have hstable : (prefixWord ++ tailWord_5496616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496616).length < 2 ^ (prefixWord ++ tailWord_5496616).sum := by decide
  have hdescent : baseEnd_5496616 < baseStart_5496616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496619 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4]
def baseStart_5496619 : Nat := 118140960795 + 5496619 * 2 ^ 59
def prefixEnd_5496619 : Nat := 4983230072969 + 3 ^ 40 * 5496619 * 2
def baseEnd_5496619 : Nat := 2822407521635735186584015

theorem tailTrace_5496619 : CollatzResearch.WordTrace tailWord_5496619 prefixEnd_5496619 2822407521635735186584015 := by
  unfold tailWord_5496619
  simp only [CollatzResearch.WordTrace]
  refine ⟨200478164873695585632780911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133652109915797057088520607 200478164873695585632780911)
  ·
    refine ⟨300717247310543378449171367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200478164873695585632780911 300717247310543378449171367)
    ·
      refine ⟨451075870965815067673757051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300717247310543378449171367 451075870965815067673757051)
      ·
        refine ⟨676613806448722601510635577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451075870965815067673757051 676613806448722601510635577)
        ·
          refine ⟨507460354836541951132976683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676613806448722601510635577 507460354836541951132976683)
          ·
            refine ⟨761190532254812926699465025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507460354836541951132976683 761190532254812926699465025)
            ·
              refine ⟨570892899191109695024598769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761190532254812926699465025 570892899191109695024598769)
              ·
                refine ⟨428169674393332271268449077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570892899191109695024598769 428169674393332271268449077)
                ·
                  refine ⟨40140906974374900431417101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428169674393332271268449077 40140906974374900431417101)
                  ·
                    refine ⟨15052840115390587661781413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40140906974374900431417101 15052840115390587661781413)
                    ·
                      refine ⟨2822407521635735186584015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15052840115390587661781413 2822407521635735186584015)
                      ·
                        rfl

theorem cell23_5496619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_5496619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496619 prefixEnd_5496619 := by exact prefixLift 5496619
  have htrace : WordTrace (prefixWord ++ tailWord_5496619) baseStart_5496619 baseEnd_5496619 := by
    simpa [prefixWord, tailWord_5496619, baseEnd_5496619] using wordTrace_append hprefix tailTrace_5496619
  have hstable : (prefixWord ++ tailWord_5496619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496619).length < 2 ^ (prefixWord ++ tailWord_5496619).sum := by decide
  have hdescent : baseEnd_5496619 < baseStart_5496619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496636 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_5496636 : Nat := 118140960795 + 5496636 * 2 ^ 59
def prefixEnd_5496636 : Nat := 4983230072969 + 3 ^ 40 * 5496636 * 2
def baseEnd_5496636 : Nat := 2822416250806861620071437

theorem tailTrace_5496636 : CollatzResearch.WordTrace tailWord_5496636 prefixEnd_5496636 2822416250806861620071437 := by
  unfold tailWord_5496636
  simp only [CollatzResearch.WordTrace]
  refine ⟨100239392457316998768074881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133652523276422665024099841 100239392457316998768074881)
  ·
    refine ⟨75179544342987749076056161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100239392457316998768074881 75179544342987749076056161)
    ·
      refine ⟨56384658257240811807042121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75179544342987749076056161 56384658257240811807042121)
      ·
        refine ⟨42288493692930608855281591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56384658257240811807042121 42288493692930608855281591)
        ·
          refine ⟨63432740539395913282922387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42288493692930608855281591 63432740539395913282922387)
          ·
            refine ⟨95149110809093869924383581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63432740539395913282922387 95149110809093869924383581)
            ·
              refine ⟨35680916553410201221643843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95149110809093869924383581 35680916553410201221643843)
              ·
                refine ⟨53521374830115301832465765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35680916553410201221643843 53521374830115301832465765)
                ·
                  refine ⟨10035257780646619093587331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53521374830115301832465765 10035257780646619093587331)
                  ·
                    refine ⟨15052886670969928640380997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10035257780646619093587331 15052886670969928640380997)
                    ·
                      refine ⟨2822416250806861620071437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15052886670969928640380997 2822416250806861620071437)
                      ·
                        rfl

theorem cell23_5496636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_5496636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496636 prefixEnd_5496636 := by exact prefixLift 5496636
  have htrace : WordTrace (prefixWord ++ tailWord_5496636) baseStart_5496636 baseEnd_5496636 := by
    simpa [prefixWord, tailWord_5496636, baseEnd_5496636] using wordTrace_append hprefix tailTrace_5496636
  have hstable : (prefixWord ++ tailWord_5496636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496636).length < 2 ^ (prefixWord ++ tailWord_5496636).sum := by decide
  have hdescent : baseEnd_5496636 < baseStart_5496636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496656 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_5496656 : Nat := 118140960795 + 5496656 * 2 ^ 59
def prefixEnd_5496656 : Nat := 4983230072969 + 3 ^ 40 * 5496656 * 2
def baseEnd_5496656 : Nat := 2822426520419951541821345

theorem tailTrace_5496656 : CollatzResearch.WordTrace tailWord_5496656 prefixEnd_5496656 2822426520419951541821345 := by
  unfold tailWord_5496656
  simp only [CollatzResearch.WordTrace]
  refine ⟨100239757187280770475938911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133653009583041027301251881 100239757187280770475938911)
  ·
    refine ⟨150359635780921155713908367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100239757187280770475938911 150359635780921155713908367)
    ·
      refine ⟨225539453671381733570862551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150359635780921155713908367 225539453671381733570862551)
      ·
        refine ⟨338309180507072600356293827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225539453671381733570862551 338309180507072600356293827)
        ·
          refine ⟨507463770760608900534440741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338309180507072600356293827 507463770760608900534440741)
          ·
            refine ⟨95149457017614168850207639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 507463770760608900534440741 95149457017614168850207639)
            ·
              refine ⟨142724185526421253275311459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95149457017614168850207639 142724185526421253275311459)
              ·
                refine ⟨214086278289631879912967189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142724185526421253275311459 214086278289631879912967189)
                ·
                  refine ⟨10035294294826494370920337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214086278289631879912967189 10035294294826494370920337)
                  ·
                    refine ⟨7526470721119870778190253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10035294294826494370920337 7526470721119870778190253)
                    ·
                      refine ⟨2822426520419951541821345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526470721119870778190253 2822426520419951541821345)
                      ·
                        rfl

theorem cell23_5496656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_5496656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496656 prefixEnd_5496656 := by exact prefixLift 5496656
  have htrace : WordTrace (prefixWord ++ tailWord_5496656) baseStart_5496656 baseEnd_5496656 := by
    simpa [prefixWord, tailWord_5496656, baseEnd_5496656] using wordTrace_append hprefix tailTrace_5496656
  have hstable : (prefixWord ++ tailWord_5496656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496656).length < 2 ^ (prefixWord ++ tailWord_5496656).sum := by decide
  have hdescent : baseEnd_5496656 < baseStart_5496656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496673 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_5496673 : Nat := 118140960795 + 5496673 * 2 ^ 59
def prefixEnd_5496673 : Nat := 4983230072969 + 3 ^ 40 * 5496673 * 2
def baseEnd_5496673 : Nat := 2822435249591077975308767

theorem tailTrace_5496673 : CollatzResearch.WordTrace tailWord_5496673 prefixEnd_5496673 2822435249591077975308767 := by
  unfold tailWord_5496673
  simp only [CollatzResearch.WordTrace]
  refine ⟨200480134415499952855246673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133653422943666635236831115 200480134415499952855246673)
  ·
    refine ⟨150360100811624964641435005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200480134415499952855246673 150360100811624964641435005)
    ·
      refine ⟨56385037804359361740538127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150360100811624964641435005 56385037804359361740538127)
      ·
        refine ⟨84577556706539042610807191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56385037804359361740538127 84577556706539042610807191)
        ·
          refine ⟨126866335059808563916210787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84577556706539042610807191 126866335059808563916210787)
          ·
            refine ⟨190299502589712845874316181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126866335059808563916210787 190299502589712845874316181)
            ·
              refine ⟨8920289183892789650358571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190299502589712845874316181 8920289183892789650358571)
              ·
                refine ⟨13380433775839184475537857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8920289183892789650358571 13380433775839184475537857)
                ·
                  refine ⟨10035325331879388356653393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13380433775839184475537857 10035325331879388356653393)
                  ·
                    refine ⟨7526493998909541267490045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10035325331879388356653393 7526493998909541267490045)
                    ·
                      refine ⟨2822435249591077975308767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526493998909541267490045 2822435249591077975308767)
                      ·
                        rfl

theorem cell23_5496673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_5496673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496673 prefixEnd_5496673 := by exact prefixLift 5496673
  have htrace : WordTrace (prefixWord ++ tailWord_5496673) baseStart_5496673 baseEnd_5496673 := by
    simpa [prefixWord, tailWord_5496673, baseEnd_5496673] using wordTrace_append hprefix tailTrace_5496673
  have hstable : (prefixWord ++ tailWord_5496673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496673).length < 2 ^ (prefixWord ++ tailWord_5496673).sum := by decide
  have hdescent : baseEnd_5496673 < baseStart_5496673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496680 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 1, 4]
def baseStart_5496680 : Nat := 118140960795 + 5496680 * 2 ^ 59
def prefixEnd_5496680 : Nat := 4983230072969 + 3 ^ 40 * 5496680 * 2
def baseEnd_5496680 : Nat := 940812947985219815973745

theorem tailTrace_5496680 : CollatzResearch.WordTrace tailWord_5496680 prefixEnd_5496680 940812947985219815973745 := by
  unfold tailWord_5496680
  simp only [CollatzResearch.WordTrace]
  refine ⟨100240194863237296525375747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133653593150983062033834329 100240194863237296525375747)
  ·
    refine ⟨150360292294855944788063621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100240194863237296525375747 150360292294855944788063621)
    ·
      refine ⟨28192554805285489647761929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150360292294855944788063621 28192554805285489647761929)
      ·
        refine ⟨21144416103964117235821447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28192554805285489647761929 21144416103964117235821447)
        ·
          refine ⟨31716624155946175853732171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21144416103964117235821447 31716624155946175853732171)
          ·
            refine ⟨47574936233919263780598257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31716624155946175853732171 47574936233919263780598257)
            ·
              refine ⟨35681202175439447835448693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47574936233919263780598257 35681202175439447835448693)
              ·
                refine ⟨3345112703947448234573315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35681202175439447835448693 3345112703947448234573315)
                ·
                  refine ⟨5017669055921172351859973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345112703947448234573315 5017669055921172351859973)
                  ·
                    refine ⟨940812947985219815973745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5017669055921172351859973 940812947985219815973745)
                    ·
                      rfl

theorem cell23_5496680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_5496680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496680 prefixEnd_5496680 := by exact prefixLift 5496680
  have htrace : WordTrace (prefixWord ++ tailWord_5496680) baseStart_5496680 baseEnd_5496680 := by
    simpa [prefixWord, tailWord_5496680, baseEnd_5496680] using wordTrace_append hprefix tailTrace_5496680
  have hstable : (prefixWord ++ tailWord_5496680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496680).length < 2 ^ (prefixWord ++ tailWord_5496680).sum := by decide
  have hdescent : baseEnd_5496680 < baseStart_5496680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496693 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 6]
def baseStart_5496693 : Nat := 118140960795 + 5496693 * 2 ^ 59
def prefixEnd_5496693 : Nat := 4983230072969 + 3 ^ 40 * 5496693 * 2
def baseEnd_5496693 : Nat := 313605057689351988562075

theorem tailTrace_5496693 : CollatzResearch.WordTrace tailWord_5496693 prefixEnd_5496693 313605057689351988562075 := by
  unfold tailWord_5496693
  simp only [CollatzResearch.WordTrace]
  refine ⟨200480863875427496270974733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133653909250284997513983155 200480863875427496270974733)
  ·
    refine ⟨75180323953285311101615525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200480863875427496270974733 75180323953285311101615525)
    ·
      refine ⟨14096310741240995831552911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75180323953285311101615525 14096310741240995831552911)
      ·
        refine ⟨21144466111861493747329367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14096310741240995831552911 21144466111861493747329367)
        ·
          refine ⟨31716699167792240620994051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21144466111861493747329367 31716699167792240620994051)
          ·
            refine ⟨47575048751688360931491077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31716699167792240620994051 47575048751688360931491077)
            ·
              refine ⟨8920321640941567674654577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47575048751688360931491077 8920321640941567674654577)
              ·
                refine ⟨6690241230706175755990933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8920321640941567674654577 6690241230706175755990933)
                ·
                  refine ⟨313605057689351988562075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6690241230706175755990933 313605057689351988562075)
                  ·
                    rfl

theorem cell23_5496693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_5496693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496693 prefixEnd_5496693 := by exact prefixLift 5496693
  have htrace : WordTrace (prefixWord ++ tailWord_5496693) baseStart_5496693 baseEnd_5496693 := by
    simpa [prefixWord, tailWord_5496693, baseEnd_5496693] using wordTrace_append hprefix tailTrace_5496693
  have hstable : (prefixWord ++ tailWord_5496693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496693).length < 2 ^ (prefixWord ++ tailWord_5496693).sum := by decide
  have hdescent : baseEnd_5496693 < baseStart_5496693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496703 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 3]
def baseStart_5496703 : Nat := 118140960795 + 5496703 * 2 ^ 59
def prefixEnd_5496703 : Nat := 4983230072969 + 3 ^ 40 * 5496703 * 2
def baseEnd_5496703 : Nat := 2822450654010712857933629

theorem tailTrace_5496703 : CollatzResearch.WordTrace tailWord_5496703 prefixEnd_5496703 2822450654010712857933629 := by
  unfold tailWord_5496703
  simp only [CollatzResearch.WordTrace]
  refine ⟨200481228605391267978838763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133654152403594178652559175 200481228605391267978838763)
  ·
    refine ⟨300721842908086901968258145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200481228605391267978838763 300721842908086901968258145)
    ·
      refine ⟨225541382181065176476193609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300721842908086901968258145 225541382181065176476193609)
      ·
        refine ⟨169156036635798882357145207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225541382181065176476193609 169156036635798882357145207)
        ·
          refine ⟨253734054953698323535717811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169156036635798882357145207 253734054953698323535717811)
          ·
            refine ⟨380601082430547485303576717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253734054953698323535717811 380601082430547485303576717)
            ·
              refine ⟨142725405911455306988841269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380601082430547485303576717 142725405911455306988841269)
              ·
                refine ⟨13380506804198935030203869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142725405911455306988841269 13380506804198935030203869)
                ·
                  refine ⟨5017690051574600636326451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13380506804198935030203869 5017690051574600636326451)
                  ·
                    refine ⟨7526535077361900954489677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017690051574600636326451 7526535077361900954489677)
                    ·
                      refine ⟨2822450654010712857933629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526535077361900954489677 2822450654010712857933629)
                      ·
                        rfl

theorem cell23_5496703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_5496703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496703 prefixEnd_5496703 := by exact prefixLift 5496703
  have htrace : WordTrace (prefixWord ++ tailWord_5496703) baseStart_5496703 baseEnd_5496703 := by
    simpa [prefixWord, tailWord_5496703, baseEnd_5496703] using wordTrace_append hprefix tailTrace_5496703
  have hstable : (prefixWord ++ tailWord_5496703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496703).length < 2 ^ (prefixWord ++ tailWord_5496703).sum := by decide
  have hdescent : baseEnd_5496703 < baseStart_5496703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496713 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 1, 5, 2]
def baseStart_5496713 : Nat := 118140960795 + 5496713 * 2 ^ 59
def prefixEnd_5496713 : Nat := 4983230072969 + 3 ^ 40 * 5496713 * 2
def baseEnd_5496713 : Nat := 2822455788817257818808583

theorem tailTrace_5496713 : CollatzResearch.WordTrace tailWord_5496713 prefixEnd_5496713 2822455788817257818808583 := by
  unfold tailWord_5496713
  simp only [CollatzResearch.WordTrace]
  refine ⟨200481593335355039686702793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133654395556903359791135195 200481593335355039686702793)
  ·
    refine ⟨150361195001516279765027095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200481593335355039686702793 150361195001516279765027095)
    ·
      refine ⟨225541792502274419647540643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150361195001516279765027095 225541792502274419647540643)
      ·
        refine ⟨338312688753411629471310965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225541792502274419647540643 338312688753411629471310965)
        ·
          refine ⟨31716814570632340262935403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338312688753411629471310965 31716814570632340262935403)
          ·
            refine ⟨47575221855948510394403105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31716814570632340262935403 47575221855948510394403105)
            ·
              refine ⟨35681416391961382795802329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47575221855948510394403105 35681416391961382795802329)
              ·
                refine ⟨26761062293971037096851747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35681416391961382795802329 26761062293971037096851747)
                ·
                  refine ⟨40141593440956555645277621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26761062293971037096851747 40141593440956555645277621)
                  ·
                    refine ⟨3763274385089677091744777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40141593440956555645277621 3763274385089677091744777)
                    ·
                      refine ⟨2822455788817257818808583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763274385089677091744777 2822455788817257818808583)
                      ·
                        rfl

theorem cell23_5496713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 5, 2].length) (baseStart_5496713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496713 prefixEnd_5496713 := by exact prefixLift 5496713
  have htrace : WordTrace (prefixWord ++ tailWord_5496713) baseStart_5496713 baseEnd_5496713 := by
    simpa [prefixWord, tailWord_5496713, baseEnd_5496713] using wordTrace_append hprefix tailTrace_5496713
  have hstable : (prefixWord ++ tailWord_5496713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496713).length < 2 ^ (prefixWord ++ tailWord_5496713).sum := by decide
  have hdescent : baseEnd_5496713 < baseStart_5496713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496730 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2]
def baseStart_5496730 : Nat := 118140960795 + 5496730 * 2 ^ 59
def prefixEnd_5496730 : Nat := 4983230072969 + 3 ^ 40 * 5496730 * 2
def baseEnd_5496730 : Nat := 2822464517988384252296005

theorem tailTrace_5496730 : CollatzResearch.WordTrace tailWord_5496730 prefixEnd_5496730 2822464517988384252296005 := by
  unfold tailWord_5496730
  simp only [CollatzResearch.WordTrace]
  refine ⟨50120553344073362897517911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133654808917528967726714429 50120553344073362897517911)
  ·
    refine ⟨75180830016110044346276867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50120553344073362897517911 75180830016110044346276867)
    ·
      refine ⟨112771245024165066519415301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75180830016110044346276867 112771245024165066519415301)
      ·
        refine ⟨21144608442030949972390369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112771245024165066519415301 21144608442030949972390369)
        ·
          refine ⟨15858456331523212479292777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21144608442030949972390369 15858456331523212479292777)
          ·
            refine ⟨11893842248642409359469583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15858456331523212479292777 11893842248642409359469583)
            ·
              refine ⟨17840763372963614039204375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11893842248642409359469583 17840763372963614039204375)
              ·
                refine ⟨26761145059445421058806563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17840763372963614039204375 26761145059445421058806563)
                ·
                  refine ⟨40141717589168131588209845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26761145059445421058806563 40141717589168131588209845)
                  ·
                    refine ⟨3763286023984512336394673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40141717589168131588209845 3763286023984512336394673)
                    ·
                      refine ⟨2822464517988384252296005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763286023984512336394673 2822464517988384252296005)
                      ·
                        rfl

theorem cell23_5496730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_5496730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496730 prefixEnd_5496730 := by exact prefixLift 5496730
  have htrace : WordTrace (prefixWord ++ tailWord_5496730) baseStart_5496730 baseEnd_5496730 := by
    simpa [prefixWord, tailWord_5496730, baseEnd_5496730] using wordTrace_append hprefix tailTrace_5496730
  have hstable : (prefixWord ++ tailWord_5496730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496730).length < 2 ^ (prefixWord ++ tailWord_5496730).sum := by decide
  have hdescent : baseEnd_5496730 < baseStart_5496730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496740 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_5496740 : Nat := 118140960795 + 5496740 * 2 ^ 59
def prefixEnd_5496740 : Nat := 4983230072969 + 3 ^ 40 * 5496740 * 2
def baseEnd_5496740 : Nat := 940823217598309737723653

theorem tailTrace_5496740 : CollatzResearch.WordTrace tailWord_5496740 prefixEnd_5496740 940823217598309737723653 := by
  unfold tailWord_5496740
  simp only [CollatzResearch.WordTrace]
  refine ⟨100241289053128611648967837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133655052070838148865290449 100241289053128611648967837)
  ·
    refine ⟨37590483394923229368362939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100241289053128611648967837 37590483394923229368362939)
    ·
      refine ⟨56385725092384844052544409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37590483394923229368362939 56385725092384844052544409)
      ·
        refine ⟨42289293819288633039408307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56385725092384844052544409 42289293819288633039408307)
        ·
          refine ⟨63433940728932949559112461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42289293819288633039408307 63433940728932949559112461)
          ·
            refine ⟨23787727773349856084667173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63433940728932949559112461 23787727773349856084667173)
            ·
              refine ⟨4460198957503098015875095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23787727773349856084667173 4460198957503098015875095)
              ·
                refine ⟨6690298436254647023812643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460198957503098015875095 6690298436254647023812643)
                ·
                  refine ⟨10035447654381970535718965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690298436254647023812643 10035447654381970535718965)
                  ·
                    refine ⟨940823217598309737723653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10035447654381970535718965 940823217598309737723653)
                    ·
                      rfl

theorem cell23_5496740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_5496740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496740 prefixEnd_5496740 := by exact prefixLift 5496740
  have htrace : WordTrace (prefixWord ++ tailWord_5496740) baseStart_5496740 baseEnd_5496740 := by
    simpa [prefixWord, tailWord_5496740, baseEnd_5496740] using wordTrace_append hprefix tailTrace_5496740
  have hstable : (prefixWord ++ tailWord_5496740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496740).length < 2 ^ (prefixWord ++ tailWord_5496740).sum := by decide
  have hdescent : baseEnd_5496740 < baseStart_5496740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496744 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 6]
def baseStart_5496744 : Nat := 118140960795 + 5496744 * 2 ^ 59
def prefixEnd_5496744 : Nat := 4983230072969 + 3 ^ 40 * 5496744 * 2
def baseEnd_5496744 : Nat := 313607967413060799724549

theorem tailTrace_5496744 : CollatzResearch.WordTrace tailWord_5496744 prefixEnd_5496744 313607967413060799724549 := by
  unfold tailWord_5496744
  simp only [CollatzResearch.WordTrace]
  refine ⟨100241361999121365990540643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133655149332161821320720857 100241361999121365990540643)
  ·
    refine ⟨150362042998682048985810965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100241361999121365990540643 150362042998682048985810965)
    ·
      refine ⟨7048220765563221046209889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150362042998682048985810965 7048220765563221046209889)
      ·
        refine ⟨5286165574172415784657417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048220765563221046209889 5286165574172415784657417)
        ·
          refine ⟨3964624180629311838493063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286165574172415784657417 3964624180629311838493063)
          ·
            refine ⟨5946936270943967757739595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964624180629311838493063 5946936270943967757739595)
            ·
              refine ⟨8920404406415951636609393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946936270943967757739595 8920404406415951636609393)
              ·
                refine ⟨6690303304811963727457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8920404406415951636609393 6690303304811963727457045)
                ·
                  refine ⟨313607967413060799724549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6690303304811963727457045 313607967413060799724549)
                  ·
                    rfl

theorem cell23_5496744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 6].length) (baseStart_5496744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496744 prefixEnd_5496744 := by exact prefixLift 5496744
  have htrace : WordTrace (prefixWord ++ tailWord_5496744) baseStart_5496744 baseEnd_5496744 := by
    simpa [prefixWord, tailWord_5496744, baseEnd_5496744] using wordTrace_append hprefix tailTrace_5496744
  have hstable : (prefixWord ++ tailWord_5496744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496744).length < 2 ^ (prefixWord ++ tailWord_5496744).sum := by decide
  have hdescent : baseEnd_5496744 < baseStart_5496744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496780 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5496780 : Nat := 118140960795 + 5496780 * 2 ^ 59
def prefixEnd_5496780 : Nat := 4983230072969 + 3 ^ 40 * 5496780 * 2
def baseEnd_5496780 : Nat := 2822490192021109056670775

theorem tailTrace_5496780 : CollatzResearch.WordTrace tailWord_5496780 prefixEnd_5496780 2822490192021109056670775 := by
  unfold tailWord_5496780
  simp only [CollatzResearch.WordTrace]
  refine ⟨100242018513056155064695897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133656024684074873419594529 100242018513056155064695897)
  ·
    refine ⟨75181513884792116298521923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100242018513056155064695897 75181513884792116298521923)
    ·
      refine ⟨112772270827188174447782885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75181513884792116298521923 112772270827188174447782885)
      ·
        refine ⟨21144800780097782708959291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112772270827188174447782885 21144800780097782708959291)
        ·
          refine ⟨31717201170146674063438937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21144800780097782708959291 31717201170146674063438937)
          ·
            refine ⟨23787900877610005547579203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31717201170146674063438937 23787900877610005547579203)
            ·
              refine ⟨35681851316415008321368805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23787900877610005547579203 35681851316415008321368805)
              ·
                refine ⟨6690347121827814060256651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35681851316415008321368805 6690347121827814060256651)
                ·
                  refine ⟨10035520682741721090384977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690347121827814060256651 10035520682741721090384977)
                  ·
                    refine ⟨7526640512056290817788733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10035520682741721090384977 7526640512056290817788733)
                    ·
                      refine ⟨2822490192021109056670775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526640512056290817788733 2822490192021109056670775)
                      ·
                        rfl

theorem cell23_5496780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5496780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496780 prefixEnd_5496780 := by exact prefixLift 5496780
  have htrace : WordTrace (prefixWord ++ tailWord_5496780) baseStart_5496780 baseEnd_5496780 := by
    simpa [prefixWord, tailWord_5496780, baseEnd_5496780] using wordTrace_append hprefix tailTrace_5496780
  have hstable : (prefixWord ++ tailWord_5496780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496780).length < 2 ^ (prefixWord ++ tailWord_5496780).sum := by decide
  have hdescent : baseEnd_5496780 < baseStart_5496780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496810 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_5496810 : Nat := 118140960795 + 5496810 * 2 ^ 59
def prefixEnd_5496810 : Nat := 4983230072969 + 3 ^ 40 * 5496810 * 2
def baseEnd_5496810 : Nat := 2822505596440743939295637

theorem tailTrace_5496810 : CollatzResearch.WordTrace tailWord_5496810 prefixEnd_5496810 2822505596440743939295637 := by
  unfold tailWord_5496810
  simp only [CollatzResearch.WordTrace]
  refine ⟨50121282804000906313245971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133656754144002416835322589 50121282804000906313245971)
  ·
    refine ⟨75181924206001359469868957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50121282804000906313245971 75181924206001359469868957)
    ·
      refine ⟨28193221577250509801200859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75181924206001359469868957 28193221577250509801200859)
      ·
        refine ⟨42289832365875764701801289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28193221577250509801200859 42289832365875764701801289)
        ·
          refine ⟨31717374274406823526350967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42289832365875764701801289 31717374274406823526350967)
          ·
            refine ⟨47576061411610235289526451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31717374274406823526350967 47576061411610235289526451)
            ·
              refine ⟨71364092117415352934289677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47576061411610235289526451 71364092117415352934289677)
              ·
                refine ⟨26761534544030757350358629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71364092117415352934289677 26761534544030757350358629)
                ·
                  refine ⟨5017787727005767003192243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26761534544030757350358629 5017787727005767003192243)
                  ·
                    refine ⟨7526681590508650504788365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017787727005767003192243 7526681590508650504788365)
                    ·
                      refine ⟨2822505596440743939295637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526681590508650504788365 2822505596440743939295637)
                      ·
                        rfl

theorem cell23_5496810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_5496810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496810 prefixEnd_5496810 := by exact prefixLift 5496810
  have htrace : WordTrace (prefixWord ++ tailWord_5496810) baseStart_5496810 baseEnd_5496810 := by
    simpa [prefixWord, tailWord_5496810, baseEnd_5496810] using wordTrace_append hprefix tailTrace_5496810
  have hstable : (prefixWord ++ tailWord_5496810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496810).length < 2 ^ (prefixWord ++ tailWord_5496810).sum := by decide
  have hdescent : baseEnd_5496810 < baseStart_5496810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496827 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 2, 1, 3]
def baseStart_5496827 : Nat := 118140960795 + 5496827 * 2 ^ 59
def prefixEnd_5496827 : Nat := 4983230072969 + 3 ^ 40 * 5496827 * 2
def baseEnd_5496827 : Nat := 2822514325611870372783059

theorem tailTrace_5496827 : CollatzResearch.WordTrace tailWord_5496827 prefixEnd_5496827 2822514325611870372783059 := by
  unfold tailWord_5496827
  simp only [CollatzResearch.WordTrace]
  refine ⟨200485751256942037156352735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133657167504628024770901823 200485751256942037156352735)
  ·
    refine ⟨300728626885413055734529103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200485751256942037156352735 300728626885413055734529103)
    ·
      refine ⟨451092940328119583601793655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300728626885413055734529103 451092940328119583601793655)
      ·
        refine ⟨676639410492179375402690483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451092940328119583601793655 676639410492179375402690483)
        ·
          refine ⟨1014959115738269063104035725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676639410492179375402690483 1014959115738269063104035725)
          ·
            refine ⟨380609668401850898664013397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1014959115738269063104035725 380609668401850898664013397)
            ·
              refine ⟨4460269551584190218718907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 380609668401850898664013397 4460269551584190218718907)
              ·
                refine ⟨6690404327376285328078361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460269551584190218718907 6690404327376285328078361)
                ·
                  refine ⟨5017803245532213996058771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6690404327376285328078361 5017803245532213996058771)
                  ·
                    refine ⟨7526704868298320994088157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017803245532213996058771 7526704868298320994088157)
                    ·
                      refine ⟨2822514325611870372783059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526704868298320994088157 2822514325611870372783059)
                      ·
                        rfl

theorem cell23_5496827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 1, 3].length) (baseStart_5496827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496827 prefixEnd_5496827 := by exact prefixLift 5496827
  have htrace : WordTrace (prefixWord ++ tailWord_5496827) baseStart_5496827 baseEnd_5496827 := by
    simpa [prefixWord, tailWord_5496827, baseEnd_5496827] using wordTrace_append hprefix tailTrace_5496827
  have hstable : (prefixWord ++ tailWord_5496827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496827).length < 2 ^ (prefixWord ++ tailWord_5496827).sum := by decide
  have hdescent : baseEnd_5496827 < baseStart_5496827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496837 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 1, 3, 2]
def baseStart_5496837 : Nat := 118140960795 + 5496837 * 2 ^ 59
def prefixEnd_5496837 : Nat := 4983230072969 + 3 ^ 40 * 5496837 * 2
def baseEnd_5496837 : Nat := 2822519460418415333658013

theorem tailTrace_5496837 : CollatzResearch.WordTrace tailWord_5496837 prefixEnd_5496837 2822519460418415333658013 := by
  unfold tailWord_5496837
  simp only [CollatzResearch.WordTrace]
  refine ⟨200486115986905808864216765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133657410657937205909477843 200486115986905808864216765)
  ·
    refine ⟨75182293495089678324081287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200486115986905808864216765 75182293495089678324081287)
    ·
      refine ⟨112773440242634517486121931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75182293495089678324081287 112773440242634517486121931)
      ·
        refine ⟨169160160363951776229182897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112773440242634517486121931 169160160363951776229182897)
        ·
          refine ⟨126870120272963832171887173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169160160363951776229182897 126870120272963832171887173)
          ·
            refine ⟨23788147551180718532228845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126870120272963832171887173 23788147551180718532228845)
            ·
              refine ⟨8920555331692769449585817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23788147551180718532228845 8920555331692769449585817)
              ·
                refine ⟨6690416498769577087189363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8920555331692769449585817 6690416498769577087189363)
                ·
                  refine ⟨10035624748154365630784045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690416498769577087189363 10035624748154365630784045)
                  ·
                    refine ⟨3763359280557887111544017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10035624748154365630784045 3763359280557887111544017)
                    ·
                      refine ⟨2822519460418415333658013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763359280557887111544017 2822519460418415333658013)
                      ·
                        rfl

theorem cell23_5496837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_5496837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496837 prefixEnd_5496837 := by exact prefixLift 5496837
  have htrace : WordTrace (prefixWord ++ tailWord_5496837) baseStart_5496837 baseEnd_5496837 := by
    simpa [prefixWord, tailWord_5496837, baseEnd_5496837] using wordTrace_append hprefix tailTrace_5496837
  have hstable : (prefixWord ++ tailWord_5496837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496837).length < 2 ^ (prefixWord ++ tailWord_5496837).sum := by decide
  have hdescent : baseEnd_5496837 < baseStart_5496837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496863 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_5496863 : Nat := 118140960795 + 5496863 * 2 ^ 59
def prefixEnd_5496863 : Nat := 4983230072969 + 3 ^ 40 * 5496863 * 2
def baseEnd_5496863 : Nat := 2822532810915432231932893

theorem tailTrace_5496863 : CollatzResearch.WordTrace tailWord_5496863 prefixEnd_5496863 2822532810915432231932893 := by
  unfold tailWord_5496863
  simp only [CollatzResearch.WordTrace]
  refine ⟨200487064284811615304663243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133658042856541076869775495 200487064284811615304663243)
  ·
    refine ⟨300730596427217422956994865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200487064284811615304663243 300730596427217422956994865)
    ·
      refine ⟨225547947320413067217746149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300730596427217422956994865 225547947320413067217746149)
      ·
        refine ⟨42290240122577450103327403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225547947320413067217746149 42290240122577450103327403)
        ·
          refine ⟨63435360183866175154991105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42290240122577450103327403 63435360183866175154991105)
          ·
            refine ⟨47576520137899631366243329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63435360183866175154991105 47576520137899631366243329)
            ·
              refine ⟨35682390103424723524682497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47576520137899631366243329 35682390103424723524682497)
              ·
                refine ⟨26761792577568542643511873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35682390103424723524682497 26761792577568542643511873)
                ·
                  refine ⟨20071344433176406982633905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26761792577568542643511873 20071344433176406982633905)
                  ·
                    refine ⟨15053508324882305236975429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20071344433176406982633905 15053508324882305236975429)
                    ·
                      refine ⟨2822532810915432231932893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15053508324882305236975429 2822532810915432231932893)
                      ·
                        rfl

theorem cell23_5496863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_5496863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496863 prefixEnd_5496863 := by exact prefixLift 5496863
  have htrace : WordTrace (prefixWord ++ tailWord_5496863) baseStart_5496863 baseEnd_5496863 := by
    simpa [prefixWord, tailWord_5496863, baseEnd_5496863] using wordTrace_append hprefix tailTrace_5496863
  have hstable : (prefixWord ++ tailWord_5496863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496863).length < 2 ^ (prefixWord ++ tailWord_5496863).sum := by decide
  have hdescent : baseEnd_5496863 < baseStart_5496863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496883 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 3]
def baseStart_5496883 : Nat := 118140960795 + 5496883 * 2 ^ 59
def prefixEnd_5496883 : Nat := 4983230072969 + 3 ^ 40 * 5496883 * 2
def baseEnd_5496883 : Nat := 2822543080528522153682801

theorem tailTrace_5496883 : CollatzResearch.WordTrace tailWord_5496883 prefixEnd_5496883 2822543080528522153682801 := by
  unfold tailWord_5496883
  simp only [CollatzResearch.WordTrace]
  refine ⟨200487793744739158720391303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133658529163159439146927535 200487793744739158720391303)
  ·
    refine ⟨300731690617108738080586955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200487793744739158720391303 300731690617108738080586955)
    ·
      refine ⟨451097535925663107120880433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300731690617108738080586955 451097535925663107120880433)
      ·
        refine ⟨338323151944247330340660325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451097535925663107120880433 338323151944247330340660325)
        ·
          refine ⟨63435590989546374438873811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 338323151944247330340660325 63435590989546374438873811)
          ·
            refine ⟨95153386484319561658310717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63435590989546374438873811 95153386484319561658310717)
            ·
              refine ⟨35682519931619835621866519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95153386484319561658310717 35682519931619835621866519)
              ·
                refine ⟨53523779897429753432799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35682519931619835621866519 53523779897429753432799779)
                ·
                  refine ⟨80285669846144630149199669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53523779897429753432799779 80285669846144630149199669)
                  ·
                    refine ⟨7526781548076059076487469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80285669846144630149199669 7526781548076059076487469)
                    ·
                      refine ⟨2822543080528522153682801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526781548076059076487469 2822543080528522153682801)
                      ·
                        rfl

theorem cell23_5496883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_5496883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496883 prefixEnd_5496883 := by exact prefixLift 5496883
  have htrace : WordTrace (prefixWord ++ tailWord_5496883) baseStart_5496883 baseEnd_5496883 := by
    simpa [prefixWord, tailWord_5496883, baseEnd_5496883] using wordTrace_append hprefix tailTrace_5496883
  have hstable : (prefixWord ++ tailWord_5496883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496883).length < 2 ^ (prefixWord ++ tailWord_5496883).sum := by decide
  have hdescent : baseEnd_5496883 < baseStart_5496883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496903 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 1, 7]
def baseStart_5496903 : Nat := 118140960795 + 5496903 * 2 ^ 59
def prefixEnd_5496903 : Nat := 4983230072969 + 3 ^ 40 * 5496903 * 2
def baseEnd_5496903 : Nat := 940851116713870691810903

theorem tailTrace_5496903 : CollatzResearch.WordTrace tailWord_5496903 prefixEnd_5496903 940851116713870691810903 := by
  unfold tailWord_5496903
  simp only [CollatzResearch.WordTrace]
  refine ⟨200488523204666702136119363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133659015469777801424079575 200488523204666702136119363)
  ·
    refine ⟨300732784807000053204179045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200488523204666702136119363 300732784807000053204179045)
    ·
      refine ⟨56387397151312509975783571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300732784807000053204179045 56387397151312509975783571)
      ·
        refine ⟨84581095726968764963675357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56387397151312509975783571 84581095726968764963675357)
        ·
          refine ⟨31717910897613286861378259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84581095726968764963675357 31717910897613286861378259)
          ·
            refine ⟨47576866346419930292067389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31717910897613286861378259 47576866346419930292067389)
            ·
              refine ⟨17841324879907473859525271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47576866346419930292067389 17841324879907473859525271)
              ·
                refine ⟨26761987319861210789287907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17841324879907473859525271 26761987319861210789287907)
                ·
                  refine ⟨40142980979791816183931861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26761987319861210789287907 40142980979791816183931861)
                  ·
                    refine ⟨940851116713870691810903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40142980979791816183931861 940851116713870691810903)
                    ·
                      rfl

theorem cell23_5496903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_5496903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496903 prefixEnd_5496903 := by exact prefixLift 5496903
  have htrace : WordTrace (prefixWord ++ tailWord_5496903) baseStart_5496903 baseEnd_5496903 := by
    simpa [prefixWord, tailWord_5496903, baseEnd_5496903] using wordTrace_append hprefix tailTrace_5496903
  have hstable : (prefixWord ++ tailWord_5496903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496903).length < 2 ^ (prefixWord ++ tailWord_5496903).sum := by decide
  have hdescent : baseEnd_5496903 < baseStart_5496903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496918 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5496918 : Nat := 118140960795 + 5496918 * 2 ^ 59
def prefixEnd_5496918 : Nat := 4983230072969 + 3 ^ 40 * 5496918 * 2
def baseEnd_5496918 : Nat := 2822561052351429516745141

theorem tailTrace_5496918 : CollatzResearch.WordTrace tailWord_5496918 prefixEnd_5496918 2822561052351429516745141 := by
  unfold tailWord_5496918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530566893725772481119713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133659380199741573131943605 12530566893725772481119713)
  ·
    refine ⟨9397925170294329360839785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12530566893725772481119713 9397925170294329360839785)
    ·
      refine ⟨7048443877720747020629839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9397925170294329360839785 7048443877720747020629839)
      ·
        refine ⟨10572665816581120530944759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7048443877720747020629839 10572665816581120530944759)
        ·
          refine ⟨15858998724871680796417139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10572665816581120530944759 15858998724871680796417139)
          ·
            refine ⟨23788498087307521194625709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15858998724871680796417139 23788498087307521194625709)
            ·
              refine ⟨8920686782740320447984641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23788498087307521194625709 8920686782740320447984641)
              ·
                refine ⟨6690515087055240335988481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8920686782740320447984641 6690515087055240335988481)
                ·
                  refine ⟨5017886315291430251991361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6690515087055240335988481 5017886315291430251991361)
                  ·
                    refine ⟨3763414736468572688993521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5017886315291430251991361 3763414736468572688993521)
                    ·
                      refine ⟨2822561052351429516745141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763414736468572688993521 2822561052351429516745141)
                      ·
                        rfl

theorem cell23_5496918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5496918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496918 prefixEnd_5496918 := by exact prefixLift 5496918
  have htrace : WordTrace (prefixWord ++ tailWord_5496918) baseStart_5496918 baseEnd_5496918 := by
    simpa [prefixWord, tailWord_5496918, baseEnd_5496918] using wordTrace_append hprefix tailTrace_5496918
  have hstable : (prefixWord ++ tailWord_5496918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496918).length < 2 ^ (prefixWord ++ tailWord_5496918).sum := by decide
  have hdescent : baseEnd_5496918 < baseStart_5496918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496960 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_5496960 : Nat := 118140960795 + 5496960 * 2 ^ 59
def prefixEnd_5496960 : Nat := 4983230072969 + 3 ^ 40 * 5496960 * 2
def baseEnd_5496960 : Nat := 2822582618538918352419947

theorem tailTrace_5496960 : CollatzResearch.WordTrace tailWord_5496960 prefixEnd_5496960 2822582618538918352419947 := by
  unfold tailWord_5496960
  simp only [CollatzResearch.WordTrace]
  refine ⟨100245301082730100435472167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133660401443640133913962889 100245301082730100435472167)
  ·
    refine ⟨150367951624095150653208251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100245301082730100435472167 150367951624095150653208251)
    ·
      refine ⟨225551927436142725979812377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150367951624095150653208251 225551927436142725979812377)
      ·
        refine ⟨169163945577107044484859283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225551927436142725979812377 169163945577107044484859283)
        ·
          refine ⟨253745918365660566727288925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169163945577107044484859283 253745918365660566727288925)
          ·
            refine ⟨95154719387122712522733347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253745918365660566727288925 95154719387122712522733347)
            ·
              refine ⟨142732079080684068784100021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95154719387122712522733347 142732079080684068784100021)
              ·
                refine ⟨13381132413814131448509377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142732079080684068784100021 13381132413814131448509377)
                ·
                  refine ⟨10035849310360598586382033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13381132413814131448509377 10035849310360598586382033)
                  ·
                    refine ⟨7526886982770448939786525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10035849310360598586382033 7526886982770448939786525)
                    ·
                      refine ⟨2822582618538918352419947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526886982770448939786525 2822582618538918352419947)
                      ·
                        rfl

theorem cell23_5496960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_5496960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496960 prefixEnd_5496960 := by exact prefixLift 5496960
  have htrace : WordTrace (prefixWord ++ tailWord_5496960) baseStart_5496960 baseEnd_5496960 := by
    simpa [prefixWord, tailWord_5496960, baseEnd_5496960] using wordTrace_append hprefix tailTrace_5496960
  have hstable : (prefixWord ++ tailWord_5496960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496960).length < 2 ^ (prefixWord ++ tailWord_5496960).sum := by decide
  have hdescent : baseEnd_5496960 < baseStart_5496960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496963 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 8]
def baseStart_5496963 : Nat := 118140960795 + 5496963 * 2 ^ 59
def prefixEnd_5496963 : Nat := 4983230072969 + 3 ^ 40 * 5496963 * 2
def baseEnd_5496963 : Nat := 313620462108986871186937

theorem tailTrace_5496963 : CollatzResearch.WordTrace tailWord_5496963 prefixEnd_5496963 313620462108986871186937 := by
  unfold tailWord_5496963
  simp only [CollatzResearch.WordTrace]
  refine ⟨200490711584449332383303543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133660474389632888255535695 200490711584449332383303543)
  ·
    refine ⟨300736067376673998574955315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200490711584449332383303543 300736067376673998574955315)
    ·
      refine ⟨451104101065010997862432973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300736067376673998574955315 451104101065010997862432973)
      ·
        refine ⟨169164037899379124198412365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451104101065010997862432973 169164037899379124198412365)
        ·
          refine ⟨63436514212267171574404637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169164037899379124198412365 63436514212267171574404637)
          ·
            refine ⟨23788692829600189340401739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63436514212267171574404637 23788692829600189340401739)
            ·
              refine ⟨35683039244400284010602609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23788692829600189340401739 35683039244400284010602609)
              ·
                refine ⟨26762279433300213007951957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35683039244400284010602609 26762279433300213007951957)
                ·
                  refine ⟨313620462108986871186937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26762279433300213007951957 313620462108986871186937)
                  ·
                    rfl

theorem cell23_5496963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 8].length) (baseStart_5496963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496963 prefixEnd_5496963 := by exact prefixLift 5496963
  have htrace : WordTrace (prefixWord ++ tailWord_5496963) baseStart_5496963 baseEnd_5496963 := by
    simpa [prefixWord, tailWord_5496963, baseEnd_5496963] using wordTrace_append hprefix tailTrace_5496963
  have hstable : (prefixWord ++ tailWord_5496963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496963).length < 2 ^ (prefixWord ++ tailWord_5496963).sum := by decide
  have hdescent : baseEnd_5496963 < baseStart_5496963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5496984 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 3, 4]
def baseStart_5496984 : Nat := 118140960795 + 5496984 * 2 ^ 59
def prefixEnd_5496984 : Nat := 4983230072969 + 3 ^ 40 * 5496984 * 2
def baseEnd_5496984 : Nat := 940864980691542086173279

theorem tailTrace_5496984 : CollatzResearch.WordTrace tailWord_5496984 prefixEnd_5496984 940864980691542086173279 := by
  unfold tailWord_5496984
  simp only [CollatzResearch.WordTrace]
  refine ⟨100245738758686626484909003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133660985011582168646545337 100245738758686626484909003)
  ·
    refine ⟨150368608138029939727363505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100245738758686626484909003 150368608138029939727363505)
    ·
      refine ⟨112776456103522454795522629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150368608138029939727363505 112776456103522454795522629)
      ·
        refine ⟨21145585519410460274160493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112776456103522454795522629 21145585519410460274160493)
        ·
          refine ⟨7929594569778922602810185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21145585519410460274160493 7929594569778922602810185)
          ·
            refine ⟨5947195927334191952107639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7929594569778922602810185 5947195927334191952107639)
            ·
              refine ⟨8920793891001287928161459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947195927334191952107639 8920793891001287928161459)
              ·
                refine ⟨13381190836501931892242189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8920793891001287928161459 13381190836501931892242189)
                ·
                  refine ⟨5017946563688224459590821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13381190836501931892242189 5017946563688224459590821)
                  ·
                    refine ⟨940864980691542086173279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5017946563688224459590821 940864980691542086173279)
                    ·
                      rfl

theorem cell23_5496984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_5496984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5496984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5496984 prefixEnd_5496984 := by exact prefixLift 5496984
  have htrace : WordTrace (prefixWord ++ tailWord_5496984) baseStart_5496984 baseEnd_5496984 := by
    simpa [prefixWord, tailWord_5496984, baseEnd_5496984] using wordTrace_append hprefix tailTrace_5496984
  have hstable : (prefixWord ++ tailWord_5496984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5496984).length < 2 ^ (prefixWord ++ tailWord_5496984).sum := by decide
  have hdescent : baseEnd_5496984 < baseStart_5496984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5496984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497010 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_5497010 : Nat := 118140960795 + 5497010 * 2 ^ 59
def prefixEnd_5497010 : Nat := 4983230072969 + 3 ^ 40 * 5497010 * 2
def baseEnd_5497010 : Nat := 940869430857214385598239

theorem tailTrace_5497010 : CollatzResearch.WordTrace tailWord_5497010 prefixEnd_5497010 940869430857214385598239 := by
  unfold tailWord_5497010
  simp only [CollatzResearch.WordTrace]
  refine ⟨50123106453819764852566121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133661617210186039606842989 50123106453819764852566121)
  ·
    refine ⟨37592329840364823639424591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50123106453819764852566121 37592329840364823639424591)
    ·
      refine ⟨56388494760547235459136887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37592329840364823639424591 56388494760547235459136887)
      ·
        refine ⟨84582742140820853188705331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56388494760547235459136887 84582742140820853188705331)
        ·
          refine ⟨126874113211231279783057997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84582742140820853188705331 126874113211231279783057997)
          ·
            refine ⟨47577792454211729918646749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126874113211231279783057997 47577792454211729918646749)
            ·
              refine ⟨17841672170329398719492531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47577792454211729918646749 17841672170329398719492531)
              ·
                refine ⟨26762508255494098079238797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17841672170329398719492531 26762508255494098079238797)
                ·
                  refine ⟨10035940595810286779714549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26762508255494098079238797 10035940595810286779714549)
                  ·
                    refine ⟨940869430857214385598239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10035940595810286779714549 940869430857214385598239)
                    ·
                      rfl

theorem cell23_5497010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_5497010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497010 prefixEnd_5497010 := by exact prefixLift 5497010
  have htrace : WordTrace (prefixWord ++ tailWord_5497010) baseStart_5497010 baseEnd_5497010 := by
    simpa [prefixWord, tailWord_5497010, baseEnd_5497010] using wordTrace_append hprefix tailTrace_5497010
  have hstable : (prefixWord ++ tailWord_5497010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497010).length < 2 ^ (prefixWord ++ tailWord_5497010).sum := by decide
  have hdescent : baseEnd_5497010 < baseStart_5497010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497041 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 1, 1, 3]
def baseStart_5497041 : Nat := 118140960795 + 5497041 * 2 ^ 59
def prefixEnd_5497041 : Nat := 4983230072969 + 3 ^ 40 * 5497041 * 2
def baseEnd_5497041 : Nat := 2822624210471932535507075

theorem tailTrace_5497041 : CollatzResearch.WordTrace tailWord_5497041 prefixEnd_5497041 2822624210471932535507075 := by
  unfold tailWord_5497041
  simp only [CollatzResearch.WordTrace]
  refine ⟨200493556478166751704642977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133662370985444501136428651 200493556478166751704642977)
  ·
    refine ⟨150370167358625063778482233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200493556478166751704642977 150370167358625063778482233)
    ·
      refine ⟨112777625518968797833861675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150370167358625063778482233 112777625518968797833861675)
      ·
        refine ⟨169166438278453196750792513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112777625518968797833861675 169166438278453196750792513)
        ·
          refine ⟨126874828708839897563094385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169166438278453196750792513 126874828708839897563094385)
          ·
            refine ⟨95156121531629923172320789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126874828708839897563094385 95156121531629923172320789)
            ·
              refine ⟨4460443196795152648702537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95156121531629923172320789 4460443196795152648702537)
              ·
                refine ⟨3345332397596364486526903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460443196795152648702537 3345332397596364486526903)
                ·
                  refine ⟨5017998596394546729790355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345332397596364486526903 5017998596394546729790355)
                  ·
                    refine ⟨7526997894591820094685533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017998596394546729790355 7526997894591820094685533)
                    ·
                      refine ⟨2822624210471932535507075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7526997894591820094685533 2822624210471932535507075)
                      ·
                        rfl

theorem cell23_5497041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_5497041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497041 prefixEnd_5497041 := by exact prefixLift 5497041
  have htrace : WordTrace (prefixWord ++ tailWord_5497041) baseStart_5497041 baseEnd_5497041 := by
    simpa [prefixWord, tailWord_5497041, baseEnd_5497041] using wordTrace_append hprefix tailTrace_5497041
  have hstable : (prefixWord ++ tailWord_5497041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497041).length < 2 ^ (prefixWord ++ tailWord_5497041).sum := by decide
  have hdescent : baseEnd_5497041 < baseStart_5497041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497050 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_5497050 : Nat := 118140960795 + 5497050 * 2 ^ 59
def prefixEnd_5497050 : Nat := 4983230072969 + 3 ^ 40 * 5497050 * 2
def baseEnd_5497050 : Nat := 2822628831797823000294533

theorem tailTrace_5497050 : CollatzResearch.WordTrace tailWord_5497050 prefixEnd_5497050 2822628831797823000294533 := by
  unfold tailWord_5497050
  simp only [CollatzResearch.WordTrace]
  refine ⟨50123471183783536560430151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133662589823422764161147069 50123471183783536560430151)
  ·
    refine ⟨75185206775675304840645227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50123471183783536560430151 75185206775675304840645227)
    ·
      refine ⟨112777810163512957260967841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75185206775675304840645227 112777810163512957260967841)
      ·
        refine ⟨84583357622634717945725881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112777810163512957260967841 84583357622634717945725881)
        ·
          refine ⟨63437518216976038459294411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84583357622634717945725881 63437518216976038459294411)
          ·
            refine ⟨95156277325464057688941617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63437518216976038459294411 95156277325464057688941617)
            ·
              refine ⟨71367207994098043266706213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95156277325464057688941617 71367207994098043266706213)
              ·
                refine ⟨13381351498893383112507415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71367207994098043266706213 13381351498893383112507415)
                ·
                  refine ⟨20072027248340074668761123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13381351498893383112507415 20072027248340074668761123)
                  ·
                    refine ⟨30108040872510112003141685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20072027248340074668761123 30108040872510112003141685)
                    ·
                      refine ⟨2822628831797823000294533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30108040872510112003141685 2822628831797823000294533)
                      ·
                        rfl

theorem cell23_5497050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_5497050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497050 prefixEnd_5497050 := by exact prefixLift 5497050
  have htrace : WordTrace (prefixWord ++ tailWord_5497050) baseStart_5497050 baseEnd_5497050 := by
    simpa [prefixWord, tailWord_5497050, baseEnd_5497050] using wordTrace_append hprefix tailTrace_5497050
  have hstable : (prefixWord ++ tailWord_5497050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497050).length < 2 ^ (prefixWord ++ tailWord_5497050).sum := by decide
  have hdescent : baseEnd_5497050 < baseStart_5497050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497057 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 2, 4]
def baseStart_5497057 : Nat := 118140960795 + 5497057 * 2 ^ 59
def prefixEnd_5497057 : Nat := 4983230072969 + 3 ^ 40 * 5497057 * 2
def baseEnd_5497057 : Nat := 940877475387468157635667

theorem tailTrace_5497057 : CollatzResearch.WordTrace tailWord_5497057 prefixEnd_5497057 940877475387468157635667 := by
  unfold tailWord_5497057
  simp only [CollatzResearch.WordTrace]
  refine ⟨200494140046108786437225425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133662760030739190958150283 200494140046108786437225425)
  ·
    refine ⟨150370605034581589827919069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200494140046108786437225425 150370605034581589827919069)
    ·
      refine ⟨56388976887968096185469651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150370605034581589827919069 56388976887968096185469651)
      ·
        refine ⟨84583465331952144278204477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56388976887968096185469651 84583465331952144278204477)
        ·
          refine ⟨31718799499482054104326679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84583465331952144278204477 31718799499482054104326679)
          ·
            refine ⟨47578199249223081156490019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31718799499482054104326679 47578199249223081156490019)
            ·
              refine ⟨71367298873834621734735029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47578199249223081156490019 71367298873834621734735029)
              ·
                refine ⟨6690684269421995787631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71367298873834621734735029 6690684269421995787631409)
                ·
                  refine ⟨5018013202066496840723557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6690684269421995787631409 5018013202066496840723557)
                  ·
                    refine ⟨940877475387468157635667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5018013202066496840723557 940877475387468157635667)
                    ·
                      rfl

theorem cell23_5497057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_5497057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497057 prefixEnd_5497057 := by exact prefixLift 5497057
  have htrace : WordTrace (prefixWord ++ tailWord_5497057) baseStart_5497057 baseEnd_5497057 := by
    simpa [prefixWord, tailWord_5497057, baseEnd_5497057] using wordTrace_append hprefix tailTrace_5497057
  have hstable : (prefixWord ++ tailWord_5497057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497057).length < 2 ^ (prefixWord ++ tailWord_5497057).sum := by decide
  have hdescent : baseEnd_5497057 < baseStart_5497057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497064 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_5497064 : Nat := 118140960795 + 5497064 * 2 ^ 59
def prefixEnd_5497064 : Nat := 4983230072969 + 3 ^ 40 * 5497064 * 2
def baseEnd_5497064 : Nat := 2822636020526985945519469

theorem tailTrace_5497064 : CollatzResearch.WordTrace tailWord_5497064 prefixEnd_5497064 2822636020526985945519469 := by
  unfold tailWord_5497064
  simp only [CollatzResearch.WordTrace]
  refine ⟨100247197678541713316365123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133662930238055617755153497 100247197678541713316365123)
  ·
    refine ⟨150370796517812569974547685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100247197678541713316365123 150370796517812569974547685)
    ·
      refine ⟨28194524347089856870227691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150370796517812569974547685 28194524347089856870227691)
      ·
        refine ⟨42291786520634785305341537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28194524347089856870227691 42291786520634785305341537)
        ·
          refine ⟨31718839890476088979006153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42291786520634785305341537 31718839890476088979006153)
          ·
            refine ⟨23789129917857066734254615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31718839890476088979006153 23789129917857066734254615)
            ·
              refine ⟨35683694876785600101381923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23789129917857066734254615 35683694876785600101381923)
              ·
                refine ⟨53525542315178400152072885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35683694876785600101381923 53525542315178400152072885)
                ·
                  refine ⟨5018019592047975014256833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53525542315178400152072885 5018019592047975014256833)
                  ·
                    refine ⟨3763514694035981260692625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018019592047975014256833 3763514694035981260692625)
                    ·
                      refine ⟨2822636020526985945519469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763514694035981260692625 2822636020526985945519469)
                      ·
                        rfl

theorem cell23_5497064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_5497064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497064 prefixEnd_5497064 := by exact prefixLift 5497064
  have htrace : WordTrace (prefixWord ++ tailWord_5497064) baseStart_5497064 baseEnd_5497064 := by
    simpa [prefixWord, tailWord_5497064, baseEnd_5497064] using wordTrace_append hprefix tailTrace_5497064
  have hstable : (prefixWord ++ tailWord_5497064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497064).length < 2 ^ (prefixWord ++ tailWord_5497064).sum := by decide
  have hdescent : baseEnd_5497064 < baseStart_5497064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497067 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 3]
def baseStart_5497067 : Nat := 118140960795 + 5497067 * 2 ^ 59
def prefixEnd_5497067 : Nat := 4983230072969 + 3 ^ 40 * 5497067 * 2
def baseEnd_5497067 : Nat := 2822637560968949433781955

theorem tailTrace_5497067 : CollatzResearch.WordTrace tailWord_5497067 prefixEnd_5497067 2822637560968949433781955 := by
  unfold tailWord_5497067
  simp only [CollatzResearch.WordTrace]
  refine ⟨200494504776072558145089455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133663003184048372096726303 200494504776072558145089455)
  ·
    refine ⟨300741757164108837217634183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200494504776072558145089455 300741757164108837217634183)
    ·
      refine ⟨451112635746163255826451275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300741757164108837217634183 451112635746163255826451275)
      ·
        refine ⟨676668953619244883739676913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451112635746163255826451275 676668953619244883739676913)
        ·
          refine ⟨507501715214433662804757685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676668953619244883739676913 507501715214433662804757685)
          ·
            refine ⟨47578285801353155887946033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 507501715214433662804757685 47578285801353155887946033)
            ·
              refine ⟨35683714351014866915959525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47578285801353155887946033 35683714351014866915959525)
              ·
                refine ⟨6690696440815287546742411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35683714351014866915959525 6690696440815287546742411)
                ·
                  refine ⟨10036044661222931320113617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690696440815287546742411 10036044661222931320113617)
                  ·
                    refine ⟨7527033495917198490085213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10036044661222931320113617 7527033495917198490085213)
                    ·
                      refine ⟨2822637560968949433781955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7527033495917198490085213 2822637560968949433781955)
                      ·
                        rfl

theorem cell23_5497067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 3].length) (baseStart_5497067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497067 prefixEnd_5497067 := by exact prefixLift 5497067
  have htrace : WordTrace (prefixWord ++ tailWord_5497067) baseStart_5497067 baseEnd_5497067 := by
    simpa [prefixWord, tailWord_5497067, baseEnd_5497067] using wordTrace_append hprefix tailTrace_5497067
  have hstable : (prefixWord ++ tailWord_5497067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497067).length < 2 ^ (prefixWord ++ tailWord_5497067).sum := by decide
  have hdescent : baseEnd_5497067 < baseStart_5497067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497084 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_5497084 : Nat := 118140960795 + 5497084 * 2 ^ 59
def prefixEnd_5497084 : Nat := 4983230072969 + 3 ^ 40 * 5497084 * 2
def baseEnd_5497084 : Nat := 2822646290140075867269377

theorem tailTrace_5497084 : CollatzResearch.WordTrace tailWord_5497084 prefixEnd_5497084 2822646290140075867269377 := by
  unfold tailWord_5497084
  simp only [CollatzResearch.WordTrace]
  refine ⟨100247562408505485024229153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133663416544673980032305537 100247562408505485024229153)
  ·
    refine ⟨75185671806379113768171865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100247562408505485024229153 75185671806379113768171865)
    ·
      refine ⟨56389253854784335326128899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75185671806379113768171865 56389253854784335326128899)
      ·
        refine ⟨84583880782176502989193349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56389253854784335326128899 84583880782176502989193349)
        ·
          refine ⟨15859477646658094310473753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84583880782176502989193349 15859477646658094310473753)
          ·
            refine ⟨11894608234993570732855315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15859477646658094310473753 11894608234993570732855315)
            ·
              refine ⟨17841912352490356099282973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11894608234993570732855315 17841912352490356099282973)
              ·
                refine ⟨6690717132183883537231115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17841912352490356099282973 6690717132183883537231115)
                ·
                  refine ⟨10036075698275825305846673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690717132183883537231115 10036075698275825305846673)
                  ·
                    refine ⟨7527056773706868979385005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10036075698275825305846673 7527056773706868979385005)
                    ·
                      refine ⟨2822646290140075867269377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7527056773706868979385005 2822646290140075867269377)
                      ·
                        rfl

theorem cell23_5497084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_5497084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497084 prefixEnd_5497084 := by exact prefixLift 5497084
  have htrace : WordTrace (prefixWord ++ tailWord_5497084) baseStart_5497084 baseEnd_5497084 := by
    simpa [prefixWord, tailWord_5497084, baseEnd_5497084] using wordTrace_append hprefix tailTrace_5497084
  have hstable : (prefixWord ++ tailWord_5497084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497084).length < 2 ^ (prefixWord ++ tailWord_5497084).sum := by decide
  have hdescent : baseEnd_5497084 < baseStart_5497084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497107 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 5, 3, 2]
def baseStart_5497107 : Nat := 118140960795 + 5497107 * 2 ^ 59
def prefixEnd_5497107 : Nat := 4983230072969 + 3 ^ 40 * 5497107 * 2
def baseEnd_5497107 : Nat := 2822658100195129277281771

theorem tailTrace_5497107 : CollatzResearch.WordTrace tailWord_5497107 prefixEnd_5497107 2822658100195129277281771 := by
  unfold tailWord_5497107
  simp only [CollatzResearch.WordTrace]
  refine ⟨200495963695927644976545575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133663975797285096651030383 200495963695927644976545575)
  ·
    refine ⟨300743945543891467464818363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200495963695927644976545575 300743945543891467464818363)
    ·
      refine ⟨451115918315837201197227545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300743945543891467464818363 451115918315837201197227545)
      ·
        refine ⟨338336938736877900897920659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451115918315837201197227545 338336938736877900897920659)
        ·
          refine ⟨507505408105316851346880989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338336938736877900897920659 507505408105316851346880989)
          ·
            refine ⟨190314528039493819255080371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507505408105316851346880989 190314528039493819255080371)
            ·
              refine ⟨285471792059240728882620557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190314528039493819255080371 285471792059240728882620557)
              ·
                refine ⟨107051922022215273330982709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285471792059240728882620557 107051922022215273330982709)
                ·
                  refine ⟨10036117689582681874779629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107051922022215273330982709 10036117689582681874779629)
                  ·
                    refine ⟨3763544133593505703042361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10036117689582681874779629 3763544133593505703042361)
                    ·
                      refine ⟨2822658100195129277281771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763544133593505703042361 2822658100195129277281771)
                      ·
                        rfl

theorem cell23_5497107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3, 2].length) (baseStart_5497107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497107 prefixEnd_5497107 := by exact prefixLift 5497107
  have htrace : WordTrace (prefixWord ++ tailWord_5497107) baseStart_5497107 baseEnd_5497107 := by
    simpa [prefixWord, tailWord_5497107, baseEnd_5497107] using wordTrace_append hprefix tailTrace_5497107
  have hstable : (prefixWord ++ tailWord_5497107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497107).length < 2 ^ (prefixWord ++ tailWord_5497107).sum := by decide
  have hdescent : baseEnd_5497107 < baseStart_5497107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497118 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5497118 : Nat := 118140960795 + 5497118 * 2 ^ 59
def prefixEnd_5497118 : Nat := 4983230072969 + 3 ^ 40 * 5497118 * 2
def baseEnd_5497118 : Nat := 2822663748482328734244221

theorem tailTrace_5497118 : CollatzResearch.WordTrace tailWord_5497118 prefixEnd_5497118 2822663748482328734244221 := by
  unfold tailWord_5497118
  simp only [CollatzResearch.WordTrace]
  refine ⟨25062045612360974231899501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133664243265925195903464005 25062045612360974231899501)
  ·
    refine ⟨9398267104635365336962313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25062045612360974231899501 9398267104635365336962313)
    ·
      refine ⟨7048700328476524002721735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9398267104635365336962313 7048700328476524002721735)
      ·
        refine ⟨10573050492714786004082603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7048700328476524002721735 10573050492714786004082603)
        ·
          refine ⟨15859575739072179006123905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573050492714786004082603 15859575739072179006123905)
          ·
            refine ⟨11894681804304134254592929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15859575739072179006123905 11894681804304134254592929)
            ·
              refine ⟨8921011353228100690944697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11894681804304134254592929 8921011353228100690944697)
              ·
                refine ⟨6690758514921075518208523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8921011353228100690944697 6690758514921075518208523)
                ·
                  refine ⟨10036137772381613277312785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690758514921075518208523 10036137772381613277312785)
                  ·
                    refine ⟨7527103329286209957984589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10036137772381613277312785 7527103329286209957984589)
                    ·
                      refine ⟨2822663748482328734244221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7527103329286209957984589 2822663748482328734244221)
                      ·
                        rfl

theorem cell23_5497118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5497118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497118 prefixEnd_5497118 := by exact prefixLift 5497118
  have htrace : WordTrace (prefixWord ++ tailWord_5497118) baseStart_5497118 baseEnd_5497118 := by
    simpa [prefixWord, tailWord_5497118, baseEnd_5497118] using wordTrace_append hprefix tailTrace_5497118
  have hstable : (prefixWord ++ tailWord_5497118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497118).length < 2 ^ (prefixWord ++ tailWord_5497118).sum := by decide
  have hdescent : baseEnd_5497118 < baseStart_5497118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497210 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_5497210 : Nat := 118140960795 + 5497210 * 2 ^ 59
def prefixEnd_5497210 : Nat := 4983230072969 + 3 ^ 40 * 5497210 * 2
def baseEnd_5497210 : Nat := 2822710988702542374293797

theorem tailTrace_5497210 : CollatzResearch.WordTrace tailWord_5497210 prefixEnd_5497210 2822710988702542374293797 := by
  unfold tailWord_5497210
  simp only [CollatzResearch.WordTrace]
  refine ⟨50124930103638623391886271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133666480276369662378363389 50124930103638623391886271)
  ·
    refine ⟨75187395155457935087829407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50124930103638623391886271 75187395155457935087829407)
    ·
      refine ⟨112781092733186902631744111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75187395155457935087829407 112781092733186902631744111)
      ·
        refine ⟨169171639099780353947616167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112781092733186902631744111 169171639099780353947616167)
        ·
          refine ⟨253757458649670530921424251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169171639099780353947616167 253757458649670530921424251)
          ·
            refine ⟨380636187974505796382136377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253757458649670530921424251 380636187974505796382136377)
            ·
              refine ⟨285477140980879347286602283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380636187974505796382136377 285477140980879347286602283)
              ·
                refine ⟨428215711471319020929903425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285477140980879347286602283 428215711471319020929903425)
                ·
                  refine ⟨321161783603489265697427569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428215711471319020929903425 321161783603489265697427569)
                  ·
                    refine ⟨240871337702616949273070677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321161783603489265697427569 240871337702616949273070677)
                    ·
                      refine ⟨2822710988702542374293797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 240871337702616949273070677 2822710988702542374293797)
                      ·
                        rfl

theorem cell23_5497210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_5497210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497210 prefixEnd_5497210 := by exact prefixLift 5497210
  have htrace : WordTrace (prefixWord ++ tailWord_5497210) baseStart_5497210 baseEnd_5497210 := by
    simpa [prefixWord, tailWord_5497210, baseEnd_5497210] using wordTrace_append hprefix tailTrace_5497210
  have hstable : (prefixWord ++ tailWord_5497210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497210).length < 2 ^ (prefixWord ++ tailWord_5497210).sum := by decide
  have hdescent : baseEnd_5497210 < baseStart_5497210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497211 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 5]
def baseStart_5497211 : Nat := 118140960795 + 5497211 * 2 ^ 59
def prefixEnd_5497211 : Nat := 4983230072969 + 3 ^ 40 * 5497211 * 2
def baseEnd_5497211 : Nat := 313634611353688541153477

theorem tailTrace_5497211 : CollatzResearch.WordTrace tailWord_5497211 prefixEnd_5497211 313634611353688541153477 := by
  unfold tailWord_5497211
  simp only [CollatzResearch.WordTrace]
  refine ⟨200499756887550870738331487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133666504591700580492220991 200499756887550870738331487)
  ·
    refine ⟨300749635331326306107497231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200499756887550870738331487 300749635331326306107497231)
    ·
      refine ⟨451124452996989459161245847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300749635331326306107497231 451124452996989459161245847)
      ·
        refine ⟨676686679495484188741868771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451124452996989459161245847 676686679495484188741868771)
        ·
          refine ⟨1015030019243226283112803157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676686679495484188741868771 1015030019243226283112803157)
          ·
            refine ⟨5947441519003279002614081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1015030019243226283112803157 5947441519003279002614081)
            ·
              refine ⟨4460581139252459251960561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947441519003279002614081 4460581139252459251960561)
              ·
                refine ⟨3345435854439344438970421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460581139252459251960561 3345435854439344438970421)
                ·
                  refine ⟨313634611353688541153477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3345435854439344438970421 313634611353688541153477)
                  ·
                    rfl

theorem cell23_5497211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 5].length) (baseStart_5497211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497211 prefixEnd_5497211 := by exact prefixLift 5497211
  have htrace : WordTrace (prefixWord ++ tailWord_5497211) baseStart_5497211 baseEnd_5497211 := by
    simpa [prefixWord, tailWord_5497211, baseEnd_5497211] using wordTrace_append hprefix tailTrace_5497211
  have hstable : (prefixWord ++ tailWord_5497211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497211).length < 2 ^ (prefixWord ++ tailWord_5497211).sum := by decide
  have hdescent : baseEnd_5497211 < baseStart_5497211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497271 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 1, 4]
def baseStart_5497271 : Nat := 118140960795 + 5497271 * 2 ^ 59
def prefixEnd_5497271 : Nat := 4983230072969 + 3 ^ 40 * 5497271 * 2
def baseEnd_5497271 : Nat := 940914103674155545210339

theorem tailTrace_5497271 : CollatzResearch.WordTrace tailWord_5497271 prefixEnd_5497271 940914103674155545210339 := by
  unfold tailWord_5497271
  simp only [CollatzResearch.WordTrace]
  refine ⟨200501945267333500985515667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133667963511555667323677111 200501945267333500985515667)
  ·
    refine ⟨300752917901000251478273501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200501945267333500985515667 300752917901000251478273501)
    ·
      refine ⟨112782344212875094304352563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300752917901000251478273501 112782344212875094304352563)
      ·
        refine ⟨169173516319312641456528845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112782344212875094304352563 169173516319312641456528845)
        ·
          refine ⟨63440068619742240546198317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169173516319312641456528845 63440068619742240546198317)
          ·
            refine ⟨23790025732403340204824369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63440068619742240546198317 23790025732403340204824369)
            ·
              refine ⟨17842519299302505153618277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23790025732403340204824369 17842519299302505153618277)
              ·
                refine ⟨3345472368619219716303427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17842519299302505153618277 3345472368619219716303427)
                ·
                  refine ⟨5018208552928829574455141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345472368619219716303427 5018208552928829574455141)
                  ·
                    refine ⟨940914103674155545210339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5018208552928829574455141 940914103674155545210339)
                    ·
                      rfl

theorem cell23_5497271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_5497271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497271 prefixEnd_5497271 := by exact prefixLift 5497271
  have htrace : WordTrace (prefixWord ++ tailWord_5497271) baseStart_5497271 baseEnd_5497271 := by
    simpa [prefixWord, tailWord_5497271, baseEnd_5497271] using wordTrace_append hprefix tailTrace_5497271
  have hstable : (prefixWord ++ tailWord_5497271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497271).length < 2 ^ (prefixWord ++ tailWord_5497271).sum := by decide
  have hdescent : baseEnd_5497271 < baseStart_5497271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497297 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_5497297 : Nat := 118140960795 + 5497297 * 2 ^ 59
def prefixEnd_5497297 : Nat := 4983230072969 + 3 ^ 40 * 5497297 * 2
def baseEnd_5497297 : Nat := 940918553839827844635299

theorem tailTrace_5497297 : CollatzResearch.WordTrace tailWord_5497297 prefixEnd_5497297 940918553839827844635299 := by
  unfold tailWord_5497297
  simp only [CollatzResearch.WordTrace]
  refine ⟨200502893565239307425962145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133668595710159538283974763 200502893565239307425962145)
  ·
    refine ⟨150377170173929480569471609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200502893565239307425962145 150377170173929480569471609)
    ·
      refine ⟨112782877630447110427103707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150377170173929480569471609 112782877630447110427103707)
      ·
        refine ⟨169174316445670665640655561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112782877630447110427103707 169174316445670665640655561)
        ·
          refine ⟨126880737334252999230491671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169174316445670665640655561 126880737334252999230491671)
          ·
            refine ⟨190321106001379498845737507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126880737334252999230491671 190321106001379498845737507)
            ·
              refine ⟨285481659002069248268606261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190321106001379498845737507 285481659002069248268606261)
              ·
                refine ⟨26763905531443992025181837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285481659002069248268606261 26763905531443992025181837)
                ·
                  refine ⟨10036464574291497009443189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26763905531443992025181837 10036464574291497009443189)
                  ·
                    refine ⟨940918553839827844635299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10036464574291497009443189 940918553839827844635299)
                    ·
                      rfl

theorem cell23_5497297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_5497297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497297 prefixEnd_5497297 := by exact prefixLift 5497297
  have htrace : WordTrace (prefixWord ++ tailWord_5497297) baseStart_5497297 baseEnd_5497297 := by
    simpa [prefixWord, tailWord_5497297, baseEnd_5497297] using wordTrace_append hprefix tailTrace_5497297
  have hstable : (prefixWord ++ tailWord_5497297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497297).length < 2 ^ (prefixWord ++ tailWord_5497297).sum := by decide
  have hdescent : baseEnd_5497297 < baseStart_5497297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497347 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6]
def baseStart_5497347 : Nat := 118140960795 + 5497347 * 2 ^ 59
def prefixEnd_5497347 : Nat := 4983230072969 + 3 ^ 40 * 5497347 * 2
def baseEnd_5497347 : Nat := 2822781335552208338280667

theorem tailTrace_5497347 : CollatzResearch.WordTrace tailWord_5497347 prefixEnd_5497347 2822781335552208338280667 := by
  unfold tailWord_5497347
  simp only [CollatzResearch.WordTrace]
  refine ⟨200504717215058165965282295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133669811476705443976854863 200504717215058165965282295)
  ·
    refine ⟨300757075822587248947923443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200504717215058165965282295 300757075822587248947923443)
    ·
      refine ⟨451135613733880873421885165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300757075822587248947923443 451135613733880873421885165)
      ·
        refine ⟨169175855150205327533206937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451135613733880873421885165 169175855150205327533206937)
        ·
          refine ⟨126881891362653995649905203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169175855150205327533206937 126881891362653995649905203)
          ·
            refine ⟨190322837043980993474857805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126881891362653995649905203 190322837043980993474857805)
            ·
              refine ⟨71371063891492872553071677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190322837043980993474857805 71371063891492872553071677)
              ·
                refine ⟨26764148959309827207401879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71371063891492872553071677 26764148959309827207401879)
                ·
                  refine ⟨40146223438964740811102819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26764148959309827207401879 40146223438964740811102819)
                  ·
                    refine ⟨60219335158447111216654229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40146223438964740811102819 60219335158447111216654229)
                    ·
                      refine ⟨2822781335552208338280667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60219335158447111216654229 2822781335552208338280667)
                      ·
                        rfl

theorem cell23_5497347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_5497347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497347 prefixEnd_5497347 := by exact prefixLift 5497347
  have htrace : WordTrace (prefixWord ++ tailWord_5497347) baseStart_5497347 baseEnd_5497347 := by
    simpa [prefixWord, tailWord_5497347, baseEnd_5497347] using wordTrace_append hprefix tailTrace_5497347
  have hstable : (prefixWord ++ tailWord_5497347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497347).length < 2 ^ (prefixWord ++ tailWord_5497347).sum := by decide
  have hdescent : baseEnd_5497347 < baseStart_5497347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497348 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_5497348 : Nat := 118140960795 + 5497348 * 2 ^ 59
def prefixEnd_5497348 : Nat := 4983230072969 + 3 ^ 40 * 5497348 * 2
def baseEnd_5497348 : Nat := 940927283010954278122721

theorem tailTrace_5497348 : CollatzResearch.WordTrace tailWord_5497348 prefixEnd_5497348 940927283010954278122721 := by
  unfold tailWord_5497348
  simp only [CollatzResearch.WordTrace]
  refine ⟨100252376844027271568034349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133669835792036362090712465 100252376844027271568034349)
  ·
    refine ⟨37594641316510226838012881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100252376844027271568034349 37594641316510226838012881)
    ·
      refine ⟨28195980987382670128509661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37594641316510226838012881 28195980987382670128509661)
      ·
        refine ⟨10573492870268501298191123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28195980987382670128509661 10573492870268501298191123)
        ·
          refine ⟨15860239305402751947286685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573492870268501298191123 15860239305402751947286685)
          ·
            refine ⟨5947589739526031980232507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15860239305402751947286685 5947589739526031980232507)
            ·
              refine ⟨8921384609289047970348761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947589739526031980232507 8921384609289047970348761)
              ·
                refine ⟨6691038456966785977761571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8921384609289047970348761 6691038456966785977761571)
                ·
                  refine ⟨10036557685450178966642357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6691038456966785977761571 10036557685450178966642357)
                  ·
                    refine ⟨940927283010954278122721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10036557685450178966642357 940927283010954278122721)
                    ·
                      rfl

theorem cell23_5497348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_5497348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497348 prefixEnd_5497348 := by exact prefixLift 5497348
  have htrace : WordTrace (prefixWord ++ tailWord_5497348) baseStart_5497348 baseEnd_5497348 := by
    simpa [prefixWord, tailWord_5497348, baseEnd_5497348] using wordTrace_append hprefix tailTrace_5497348
  have hstable : (prefixWord ++ tailWord_5497348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497348).length < 2 ^ (prefixWord ++ tailWord_5497348).sum := by decide
  have hdescent : baseEnd_5497348 < baseStart_5497348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497351 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_5497351 : Nat := 118140960795 + 5497351 * 2 ^ 59
def prefixEnd_5497351 : Nat := 4983230072969 + 3 ^ 40 * 5497351 * 2
def baseEnd_5497351 : Nat := 2822783389474826322630649

theorem tailTrace_5497351 : CollatzResearch.WordTrace tailWord_5497351 prefixEnd_5497351 2822783389474826322630649 := by
  unfold tailWord_5497351
  simp only [CollatzResearch.WordTrace]
  refine ⟨200504863107043674648427907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133669908738029116432285271 200504863107043674648427907)
  ·
    refine ⟨300757294660565511972641861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200504863107043674648427907 300757294660565511972641861)
    ·
      refine ⟨56391992748856033494870349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300757294660565511972641861 56391992748856033494870349)
      ·
        refine ⟨21146997280821012560576381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56391992748856033494870349 21146997280821012560576381)
        ·
          refine ⟨7930123980307879710216143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21146997280821012560576381 7930123980307879710216143)
          ·
            refine ⟨11895185970461819565324215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7930123980307879710216143 11895185970461819565324215)
            ·
              refine ⟨17842778955692729347986323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11895185970461819565324215 17842778955692729347986323)
              ·
                refine ⟨26764168433539094021979485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17842778955692729347986323 26764168433539094021979485)
                ·
                  refine ⟨10036563162577160258242307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26764168433539094021979485 10036563162577160258242307)
                  ·
                    refine ⟨15054844743865740387363461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10036563162577160258242307 15054844743865740387363461)
                    ·
                      refine ⟨2822783389474826322630649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15054844743865740387363461 2822783389474826322630649)
                      ·
                        rfl

theorem cell23_5497351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_5497351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497351 prefixEnd_5497351 := by exact prefixLift 5497351
  have htrace : WordTrace (prefixWord ++ tailWord_5497351) baseStart_5497351 baseEnd_5497351 := by
    simpa [prefixWord, tailWord_5497351, baseEnd_5497351] using wordTrace_append hprefix tailTrace_5497351
  have hstable : (prefixWord ++ tailWord_5497351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497351).length < 2 ^ (prefixWord ++ tailWord_5497351).sum := by decide
  have hdescent : baseEnd_5497351 < baseStart_5497351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497368 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 1, 1, 4]
def baseStart_5497368 : Nat := 118140960795 + 5497368 * 2 ^ 59
def prefixEnd_5497368 : Nat := 4983230072969 + 3 ^ 40 * 5497368 * 2
def baseEnd_5497368 : Nat := 2822792118645952756118071

theorem tailTrace_5497368 : CollatzResearch.WordTrace tailWord_5497368 prefixEnd_5497368 2822792118645952756118071 := by
  unfold tailWord_5497368
  simp only [CollatzResearch.WordTrace]
  refine ⟨100252741573991043275898379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133670322098654724367864505 100252741573991043275898379)
  ·
    refine ⟨150379112360986564913847569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100252741573991043275898379 150379112360986564913847569)
    ·
      refine ⟨112784334270739923685385677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150379112360986564913847569 112784334270739923685385677)
      ·
        refine ⟨42294125351527471382019629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112784334270739923685385677 42294125351527471382019629)
        ·
          refine ⟨15860297006822801768257361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42294125351527471382019629 15860297006822801768257361)
          ·
            refine ⟨11895222755117101326193021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15860297006822801768257361 11895222755117101326193021)
            ·
              refine ⟨4460708533168912997322383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11895222755117101326193021 4460708533168912997322383)
              ·
                refine ⟨6691062799753369495983575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460708533168912997322383 6691062799753369495983575)
                ·
                  refine ⟨10036594199630054243975363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6691062799753369495983575 10036594199630054243975363)
                  ·
                    refine ⟨15054891299445081365963045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10036594199630054243975363 15054891299445081365963045)
                    ·
                      refine ⟨2822792118645952756118071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15054891299445081365963045 2822792118645952756118071)
                      ·
                        rfl

theorem cell23_5497368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_5497368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497368 prefixEnd_5497368 := by exact prefixLift 5497368
  have htrace : WordTrace (prefixWord ++ tailWord_5497368) baseStart_5497368 baseEnd_5497368 := by
    simpa [prefixWord, tailWord_5497368, baseEnd_5497368] using wordTrace_append hprefix tailTrace_5497368
  have hstable : (prefixWord ++ tailWord_5497368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497368).length < 2 ^ (prefixWord ++ tailWord_5497368).sum := by decide
  have hdescent : baseEnd_5497368 < baseStart_5497368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497398 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5497398 : Nat := 118140960795 + 5497398 * 2 ^ 59
def prefixEnd_5497398 : Nat := 4983230072969 + 3 ^ 40 * 5497398 * 2
def baseEnd_5497398 : Nat := 2822807523065587638742933

theorem tailTrace_5497398 : CollatzResearch.WordTrace tailWord_5497398 prefixEnd_5497398 2822807523065587638742933 := by
  unfold tailWord_5497398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12531661083617087604711803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133671051558582267783592565 12531661083617087604711803)
  ·
    refine ⟨18797491625425631407067705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12531661083617087604711803 18797491625425631407067705)
    ·
      refine ⟨14098118719069223555300779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18797491625425631407067705 14098118719069223555300779)
      ·
        refine ⟨21147178078603835332951169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14098118719069223555300779 21147178078603835332951169)
        ·
          refine ⟨15860383558952876499713377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21147178078603835332951169 15860383558952876499713377)
          ·
            refine ⟨11895287669214657374785033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15860383558952876499713377 11895287669214657374785033)
            ·
              refine ⟨8921465751910993031088775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11895287669214657374785033 8921465751910993031088775)
              ·
                refine ⟨13382198627866489546633163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8921465751910993031088775 13382198627866489546633163)
                ·
                  refine ⟨20073297941799734319949745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13382198627866489546633163 20073297941799734319949745)
                  ·
                    refine ⟨15054973456349800739962309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20073297941799734319949745 15054973456349800739962309)
                    ·
                      refine ⟨2822807523065587638742933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15054973456349800739962309 2822807523065587638742933)
                      ·
                        rfl

theorem cell23_5497398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5497398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497398 prefixEnd_5497398 := by exact prefixLift 5497398
  have htrace : WordTrace (prefixWord ++ tailWord_5497398) baseStart_5497398 baseEnd_5497398 := by
    simpa [prefixWord, tailWord_5497398, baseEnd_5497398] using wordTrace_append hprefix tailTrace_5497398
  have hstable : (prefixWord ++ tailWord_5497398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497398).length < 2 ^ (prefixWord ++ tailWord_5497398).sum := by decide
  have hdescent : baseEnd_5497398 < baseStart_5497398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497401 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5497401 : Nat := 118140960795 + 5497401 * 2 ^ 59
def prefixEnd_5497401 : Nat := 4983230072969 + 3 ^ 40 * 5497401 * 2
def baseEnd_5497401 : Nat := 2822809063507551127005419

theorem tailTrace_5497401 : CollatzResearch.WordTrace tailWord_5497401 prefixEnd_5497401 2822809063507551127005419 := by
  unfold tailWord_5497401
  simp only [CollatzResearch.WordTrace]
  refine ⟨200506686756862533187748057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133671124504575022125165371 200506686756862533187748057)
  ·
    refine ⟨150380015067646899890811043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200506686756862533187748057 150380015067646899890811043)
    ·
      refine ⟨225570022601470349836216565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150380015067646899890811043 225570022601470349836216565)
      ·
        refine ⟨21147189618887845297145303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225570022601470349836216565 21147189618887845297145303)
        ·
          refine ⟨31720784428331767945717955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21147189618887845297145303 31720784428331767945717955)
          ·
            refine ⟨47581176642497651918576933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31720784428331767945717955 47581176642497651918576933)
            ·
              refine ⟨8921470620468309734733175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47581176642497651918576933 8921470620468309734733175)
              ·
                refine ⟨13382205930702464602099763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8921470620468309734733175 13382205930702464602099763)
                ·
                  refine ⟨20073308896053696903149645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13382205930702464602099763 20073308896053696903149645)
                  ·
                    refine ⟨7527490836020136338681117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20073308896053696903149645 7527490836020136338681117)
                    ·
                      refine ⟨2822809063507551127005419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7527490836020136338681117 2822809063507551127005419)
                      ·
                        rfl

theorem cell23_5497401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5497401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497401 prefixEnd_5497401 := by exact prefixLift 5497401
  have htrace : WordTrace (prefixWord ++ tailWord_5497401) baseStart_5497401 baseEnd_5497401 := by
    simpa [prefixWord, tailWord_5497401, baseEnd_5497401] using wordTrace_append hprefix tailTrace_5497401
  have hstable : (prefixWord ++ tailWord_5497401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497401).length < 2 ^ (prefixWord ++ tailWord_5497401).sum := by decide
  have hdescent : baseEnd_5497401 < baseStart_5497401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497462 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5497462 : Nat := 118140960795 + 5497462 * 2 ^ 59
def prefixEnd_5497462 : Nat := 4983230072969 + 3 ^ 40 * 5497462 * 2
def baseEnd_5497462 : Nat := 2822840385827475388342639

theorem tailTrace_5497462 : CollatzResearch.WordTrace tailWord_5497462 prefixEnd_5497462 2822840385827475388342639 := by
  unfold tailWord_5497462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12531806975602596287857415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133672607739761027070479093 12531806975602596287857415)
  ·
    refine ⟨18797710463403894431786123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12531806975602596287857415 18797710463403894431786123)
    ·
      refine ⟨28196565695105841647679185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18797710463403894431786123 28196565695105841647679185)
      ·
        refine ⟨21147424271329381235759389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28196565695105841647679185 21147424271329381235759389)
        ·
          refine ⟨7930284101748517963409771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21147424271329381235759389 7930284101748517963409771)
          ·
            refine ⟨11895426152622776945114657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7930284101748517963409771 11895426152622776945114657)
            ·
              refine ⟨8921569614467082708835993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11895426152622776945114657 8921569614467082708835993)
              ·
                refine ⟨6691177210850312031626995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8921569614467082708835993 6691177210850312031626995)
                ·
                  refine ⟨10036765816275468047440493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6691177210850312031626995 10036765816275468047440493)
                  ·
                    refine ⟨3763787181103300517790185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10036765816275468047440493 3763787181103300517790185)
                    ·
                      refine ⟨2822840385827475388342639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763787181103300517790185 2822840385827475388342639)
                      ·
                        rfl

theorem cell23_5497462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5497462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497462 prefixEnd_5497462 := by exact prefixLift 5497462
  have htrace : WordTrace (prefixWord ++ tailWord_5497462) baseStart_5497462 baseEnd_5497462 := by
    simpa [prefixWord, tailWord_5497462, baseEnd_5497462] using wordTrace_append hprefix tailTrace_5497462
  have hstable : (prefixWord ++ tailWord_5497462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497462).length < 2 ^ (prefixWord ++ tailWord_5497462).sum := by decide
  have hdescent : baseEnd_5497462 < baseStart_5497462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497531 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 6, 4, 2]
def baseStart_5497531 : Nat := 118140960795 + 5497531 * 2 ^ 59
def prefixEnd_5497531 : Nat := 4983230072969 + 3 ^ 40 * 5497531 * 2
def baseEnd_5497531 : Nat := 2822875815992635618379821

theorem tailTrace_5497531 : CollatzResearch.WordTrace tailWord_5497531 prefixEnd_5497531 2822875815992635618379821 := by
  unfold tailWord_5497531
  simp only [CollatzResearch.WordTrace]
  refine ⟨200511428246391565389980447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133674285497594376926653631 200511428246391565389980447)
  ·
    refine ⟨300767142369587348084970671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200511428246391565389980447 300767142369587348084970671)
    ·
      refine ⟨451150713554381022127456007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300767142369587348084970671 451150713554381022127456007)
      ·
        refine ⟨676726070331571533191184011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451150713554381022127456007 676726070331571533191184011)
        ·
          refine ⟨1015089105497357299786776017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676726070331571533191184011 1015089105497357299786776017)
          ·
            refine ⟨761316829123017974840082013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015089105497357299786776017 761316829123017974840082013)
            ·
              refine ⟨285493810921131740565030755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 761316829123017974840082013 285493810921131740565030755)
              ·
                refine ⟨428240716381697610847546133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285493810921131740565030755 428240716381697610847546133)
                ·
                  refine ⟨20073783580392075508478725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 428240716381697610847546133 20073783580392075508478725)
                  ·
                    refine ⟨3763834421323514157839761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20073783580392075508478725 3763834421323514157839761)
                    ·
                      refine ⟨2822875815992635618379821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763834421323514157839761 2822875815992635618379821)
                      ·
                        rfl

theorem cell23_5497531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4, 2].length) (baseStart_5497531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497531 prefixEnd_5497531 := by exact prefixLift 5497531
  have htrace : WordTrace (prefixWord ++ tailWord_5497531) baseStart_5497531 baseEnd_5497531 := by
    simpa [prefixWord, tailWord_5497531, baseEnd_5497531] using wordTrace_append hprefix tailTrace_5497531
  have hstable : (prefixWord ++ tailWord_5497531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497531).length < 2 ^ (prefixWord ++ tailWord_5497531).sum := by decide
  have hdescent : baseEnd_5497531 < baseStart_5497531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497548 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5497548 : Nat := 118140960795 + 5497548 * 2 ^ 59
def prefixEnd_5497548 : Nat := 4983230072969 + 3 ^ 40 * 5497548 * 2
def baseEnd_5497548 : Nat := 2822884545163762051867243

theorem tailTrace_5497548 : CollatzResearch.WordTrace tailWord_5497548 prefixEnd_5497548 2822884545163762051867243 := by
  unfold tailWord_5497548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100256024143664988646674649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133674698858219984862232865 100256024143664988646674649)
  ·
    refine ⟨75192018107748741485005987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100256024143664988646674649 75192018107748741485005987)
    ·
      refine ⟨112788027161623112227508981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75192018107748741485005987 112788027161623112227508981)
      ·
        refine ⟨10573877546402166771328967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112788027161623112227508981 10573877546402166771328967)
        ·
          refine ⟨15860816319603250156993451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573877546402166771328967 15860816319603250156993451)
          ·
            refine ⟨23791224479404875235490177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15860816319603250156993451 23791224479404875235490177)
            ·
              refine ⟨17843418359553656426617633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23791224479404875235490177 17843418359553656426617633)
              ·
                refine ⟨13382563769665242319963225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17843418359553656426617633 13382563769665242319963225)
                ·
                  refine ⟨10036922827248931739972419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13382563769665242319963225 10036922827248931739972419)
                  ·
                    refine ⟨15055384240873397609958629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10036922827248931739972419 15055384240873397609958629)
                    ·
                      refine ⟨2822884545163762051867243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15055384240873397609958629 2822884545163762051867243)
                      ·
                        rfl

theorem cell23_5497548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5497548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497548 prefixEnd_5497548 := by exact prefixLift 5497548
  have htrace : WordTrace (prefixWord ++ tailWord_5497548) baseStart_5497548 baseEnd_5497548 := by
    simpa [prefixWord, tailWord_5497548, baseEnd_5497548] using wordTrace_append hprefix tailTrace_5497548
  have hstable : (prefixWord ++ tailWord_5497548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497548).length < 2 ^ (prefixWord ++ tailWord_5497548).sum := by decide
  have hdescent : baseEnd_5497548 < baseStart_5497548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497549 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 5]
def baseStart_5497549 : Nat := 118140960795 + 5497549 * 2 ^ 59
def prefixEnd_5497549 : Nat := 4983230072969 + 3 ^ 40 * 5497549 * 2
def baseEnd_5497549 : Nat := 313653895404935171994971

theorem tailTrace_5497549 : CollatzResearch.WordTrace tailWord_5497549 prefixEnd_5497549 313653895404935171994971 := by
  unfold tailWord_5497549
  simp only [CollatzResearch.WordTrace]
  refine ⟨200512084760326354464135701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133674723173550902976090467 200512084760326354464135701)
  ·
    refine ⟨9399003973140297865506361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200512084760326354464135701 9399003973140297865506361)
    ·
      refine ⟨7049252979855223399129771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9399003973140297865506361 7049252979855223399129771)
      ·
        refine ⟨10573879469782835098694657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7049252979855223399129771 10573879469782835098694657)
        ·
          refine ⟨7930409602337126324020993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10573879469782835098694657 7930409602337126324020993)
          ·
            refine ⟨5947807201752844743015745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930409602337126324020993 5947807201752844743015745)
            ·
              refine ⟨4460855401314633557261809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5947807201752844743015745 4460855401314633557261809)
              ·
                refine ⟨3345641550985975167946357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460855401314633557261809 3345641550985975167946357)
                ·
                  refine ⟨313653895404935171994971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3345641550985975167946357 313653895404935171994971)
                  ·
                    rfl

theorem cell23_5497549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_5497549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497549 prefixEnd_5497549 := by exact prefixLift 5497549
  have htrace : WordTrace (prefixWord ++ tailWord_5497549) baseStart_5497549 baseEnd_5497549 := by
    simpa [prefixWord, tailWord_5497549, baseEnd_5497549] using wordTrace_append hprefix tailTrace_5497549
  have hstable : (prefixWord ++ tailWord_5497549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497549).length < 2 ^ (prefixWord ++ tailWord_5497549).sum := by decide
  have hdescent : baseEnd_5497549 < baseStart_5497549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497615 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 1, 1, 3]
def baseStart_5497615 : Nat := 118140960795 + 5497615 * 2 ^ 59
def prefixEnd_5497615 : Nat := 4983230072969 + 3 ^ 40 * 5497615 * 2
def baseEnd_5497615 : Nat := 2822918948367613289729435

theorem tailTrace_5497615 : CollatzResearch.WordTrace tailWord_5497615 prefixEnd_5497615 2822918948367613289729435 := by
  unfold tailWord_5497615
  simp only [CollatzResearch.WordTrace]
  refine ⟨200514491978087247736038299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133676327985391498490692199 200514491978087247736038299)
  ·
    refine ⟨300771737967130871604057449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200514491978087247736038299 300771737967130871604057449)
    ·
      refine ⟨225578803475348153703043087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300771737967130871604057449 225578803475348153703043087)
      ·
        refine ⟨338368205213022230554564631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225578803475348153703043087 338368205213022230554564631)
        ·
          refine ⟨507552307819533345831846947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338368205213022230554564631 507552307819533345831846947)
          ·
            refine ⟨761328461729300018747770421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507552307819533345831846947 761328461729300018747770421)
            ·
              refine ⟨71374543287121876757603477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 761328461729300018747770421 71374543287121876757603477)
              ·
                refine ⟨3345681716583837973012663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71374543287121876757603477 3345681716583837973012663)
                ·
                  refine ⟨5018522574875756959518995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345681716583837973012663 5018522574875756959518995)
                  ·
                    refine ⟨7527783862313635439278493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5018522574875756959518995 7527783862313635439278493)
                    ·
                      refine ⟨2822918948367613289729435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7527783862313635439278493 2822918948367613289729435)
                      ·
                        rfl

theorem cell23_5497615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 1, 3].length) (baseStart_5497615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497615 prefixEnd_5497615 := by exact prefixLift 5497615
  have htrace : WordTrace (prefixWord ++ tailWord_5497615) baseStart_5497615 baseEnd_5497615 := by
    simpa [prefixWord, tailWord_5497615, baseEnd_5497615] using wordTrace_append hprefix tailTrace_5497615
  have hstable : (prefixWord ++ tailWord_5497615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497615).length < 2 ^ (prefixWord ++ tailWord_5497615).sum := by decide
  have hdescent : baseEnd_5497615 < baseStart_5497615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497692 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5497692 : Nat := 118140960795 + 5497692 * 2 ^ 59
def prefixEnd_5497692 : Nat := 4983230072969 + 3 ^ 40 * 5497692 * 2
def baseEnd_5497692 : Nat := 2822958486378009488466581

theorem tailTrace_5497692 : CollatzResearch.WordTrace tailWord_5497692 prefixEnd_5497692 2822958486378009488466581 := by
  unfold tailWord_5497692
  simp only [CollatzResearch.WordTrace]
  refine ⟨100258650199404144943295665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133678200265872193257727553 100258650199404144943295665)
  ·
    refine ⟨75193987649553108707471749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100258650199404144943295665 75193987649553108707471749)
    ·
      refine ⟨14098872684291207882650953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75193987649553108707471749 14098872684291207882650953)
      ·
        refine ⟨10574154513218405911988215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14098872684291207882650953 10574154513218405911988215)
        ·
          refine ⟨15861231769827608867982323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10574154513218405911988215 15861231769827608867982323)
          ·
            refine ⟨23791847654741413301973485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15861231769827608867982323 23791847654741413301973485)
            ·
              refine ⟨8921942870528029988240057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23791847654741413301973485 8921942870528029988240057)
              ·
                refine ⟨6691457152896022491180043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8921942870528029988240057 6691457152896022491180043)
                ·
                  refine ⟨10037185729344033736770065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6691457152896022491180043 10037185729344033736770065)
                  ·
                    refine ⟨7527889297008025302577549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10037185729344033736770065 7527889297008025302577549)
                    ·
                      refine ⟨2822958486378009488466581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7527889297008025302577549 2822958486378009488466581)
                      ·
                        rfl

theorem cell23_5497692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5497692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497692 prefixEnd_5497692 := by exact prefixLift 5497692
  have htrace : WordTrace (prefixWord ++ tailWord_5497692) baseStart_5497692 baseEnd_5497692 := by
    simpa [prefixWord, tailWord_5497692, baseEnd_5497692] using wordTrace_append hprefix tailTrace_5497692
  have hstable : (prefixWord ++ tailWord_5497692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497692).length < 2 ^ (prefixWord ++ tailWord_5497692).sum := by decide
  have hdescent : baseEnd_5497692 < baseStart_5497692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497701 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_5497701 : Nat := 118140960795 + 5497701 * 2 ^ 59
def prefixEnd_5497701 : Nat := 4983230072969 + 3 ^ 40 * 5497701 * 2
def baseEnd_5497701 : Nat := 2822963107703899953254039

theorem tailTrace_5497701 : CollatzResearch.WordTrace tailWord_5497701 prefixEnd_5497701 2822963107703899953254039 := by
  unfold tailWord_5497701
  simp only [CollatzResearch.WordTrace]
  refine ⟨200517628655775684423668957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133678419103850456282445971 200517628655775684423668957)
  ·
    refine ⟨75194110745915881658875859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200517628655775684423668957 75194110745915881658875859)
    ·
      refine ⟨112791166118873822488313789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75194110745915881658875859 112791166118873822488313789)
      ·
        refine ⟨42296687294577683433117671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112791166118873822488313789 42296687294577683433117671)
        ·
          refine ⟨63445030941866525149676507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42296687294577683433117671 63445030941866525149676507)
          ·
            refine ⟨95167546412799787724514761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63445030941866525149676507 95167546412799787724514761)
            ·
              refine ⟨71375659809599840793386071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95167546412799787724514761 71375659809599840793386071)
              ·
                refine ⟨107063489714399761190079107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71375659809599840793386071 107063489714399761190079107)
                ·
                  refine ⟨160595234571599641785118661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107063489714399761190079107 160595234571599641785118661)
                  ·
                    refine ⟨30111606482174932834709749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160595234571599641785118661 30111606482174932834709749)
                    ·
                      refine ⟨2822963107703899953254039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30111606482174932834709749 2822963107703899953254039)
                      ·
                        rfl

theorem cell23_5497701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_5497701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497701 prefixEnd_5497701 := by exact prefixLift 5497701
  have htrace : WordTrace (prefixWord ++ tailWord_5497701) baseStart_5497701 baseEnd_5497701 := by
    simpa [prefixWord, tailWord_5497701, baseEnd_5497701] using wordTrace_append hprefix tailTrace_5497701
  have hstable : (prefixWord ++ tailWord_5497701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497701).length < 2 ^ (prefixWord ++ tailWord_5497701).sum := by decide
  have hdescent : baseEnd_5497701 < baseStart_5497701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497711 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_5497711 : Nat := 118140960795 + 5497711 * 2 ^ 59
def prefixEnd_5497711 : Nat := 4983230072969 + 3 ^ 40 * 5497711 * 2
def baseEnd_5497711 : Nat := 2822968242510444914128993

theorem tailTrace_5497711 : CollatzResearch.WordTrace tailWord_5497711 prefixEnd_5497711 2822968242510444914128993 := by
  unfold tailWord_5497711
  simp only [CollatzResearch.WordTrace]
  refine ⟨200517993385739456131532987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133678662257159637421021991 200517993385739456131532987)
  ·
    refine ⟨300776990078609184197299481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200517993385739456131532987 300776990078609184197299481)
    ·
      refine ⟨225582742558956888147974611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300776990078609184197299481 225582742558956888147974611)
      ·
        refine ⟨338374113838435332221961917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225582742558956888147974611 338374113838435332221961917)
        ·
          refine ⟨126890292689413249583235719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338374113838435332221961917 126890292689413249583235719)
          ·
            refine ⟨190335439034119874374853579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126890292689413249583235719 190335439034119874374853579)
            ·
              refine ⟨285503158551179811562280369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190335439034119874374853579 285503158551179811562280369)
              ·
                refine ⟨214127368913384858671710277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285503158551179811562280369 214127368913384858671710277)
                ·
                  refine ⟨40148881671259661000945677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214127368913384858671710277 40148881671259661000945677)
                  ·
                    refine ⟨15055830626722372875354629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40148881671259661000945677 15055830626722372875354629)
                    ·
                      refine ⟨2822968242510444914128993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15055830626722372875354629 2822968242510444914128993)
                      ·
                        rfl

theorem cell23_5497711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_5497711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497711 prefixEnd_5497711 := by exact prefixLift 5497711
  have htrace : WordTrace (prefixWord ++ tailWord_5497711) baseStart_5497711 baseEnd_5497711 := by
    simpa [prefixWord, tailWord_5497711, baseEnd_5497711] using wordTrace_append hprefix tailTrace_5497711
  have hstable : (prefixWord ++ tailWord_5497711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497711).length < 2 ^ (prefixWord ++ tailWord_5497711).sum := by decide
  have hdescent : baseEnd_5497711 < baseStart_5497711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497715 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 1, 3, 2]
def baseStart_5497715 : Nat := 118140960795 + 5497715 * 2 ^ 59
def prefixEnd_5497715 : Nat := 4983230072969 + 3 ^ 40 * 5497715 * 2
def baseEnd_5497715 : Nat := 2822970296433062898478975

theorem tailTrace_5497715 : CollatzResearch.WordTrace tailWord_5497715 prefixEnd_5497715 2822970296433062898478975 := by
  unfold tailWord_5497715
  simp only [CollatzResearch.WordTrace]
  refine ⟨200518139277724964814678599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133678759518483309876452399 200518139277724964814678599)
  ·
    refine ⟨300777208916587447222017899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200518139277724964814678599 300777208916587447222017899)
    ·
      refine ⟨451165813374881170833026849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300777208916587447222017899 451165813374881170833026849)
      ·
        refine ⟨338374360031160878124770137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451165813374881170833026849 338374360031160878124770137)
        ·
          refine ⟨253780770023370658593577603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338374360031160878124770137 253780770023370658593577603)
          ·
            refine ⟨380671155035055987890366405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253780770023370658593577603 380671155035055987890366405)
            ·
              refine ⟨71375841569072997729443701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 380671155035055987890366405 71375841569072997729443701)
              ·
                refine ⟨6691485147100593537135347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71375841569072997729443701 6691485147100593537135347)
                ·
                  refine ⟨10037227720650890305703021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6691485147100593537135347 10037227720650890305703021)
                  ·
                    refine ⟨3763960395244083864638633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10037227720650890305703021 3763960395244083864638633)
                    ·
                      refine ⟨2822970296433062898478975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763960395244083864638633 2822970296433062898478975)
                      ·
                        rfl

theorem cell23_5497715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 3, 2].length) (baseStart_5497715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497715 prefixEnd_5497715 := by exact prefixLift 5497715
  have htrace : WordTrace (prefixWord ++ tailWord_5497715) baseStart_5497715 baseEnd_5497715 := by
    simpa [prefixWord, tailWord_5497715, baseEnd_5497715] using wordTrace_append hprefix tailTrace_5497715
  have hstable : (prefixWord ++ tailWord_5497715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497715).length < 2 ^ (prefixWord ++ tailWord_5497715).sum := by decide
  have hdescent : baseEnd_5497715 < baseStart_5497715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497738 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_5497738 : Nat := 118140960795 + 5497738 * 2 ^ 59
def prefixEnd_5497738 : Nat := 4983230072969 + 3 ^ 40 * 5497738 * 2
def baseEnd_5497738 : Nat := 940994035496038769497123

theorem tailTrace_5497738 : CollatzResearch.WordTrace tailWord_5497738 prefixEnd_5497738 940994035496038769497123 := by
  unfold tailWord_5497738
  simp only [CollatzResearch.WordTrace]
  refine ⟨50129744539160409935691467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133679318771094426495177245 50129744539160409935691467)
  ·
    refine ⟨75194616808740614903537201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50129744539160409935691467 75194616808740614903537201)
    ·
      refine ⟨56395962606555461177652901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75194616808740614903537201 56395962606555461177652901)
      ·
        refine ⟨10574242988729148970809919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56395962606555461177652901 10574242988729148970809919)
        ·
          refine ⟨15861364483093723456214879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10574242988729148970809919 15861364483093723456214879)
          ·
            refine ⟨23792046724640585184322319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15861364483093723456214879 23792046724640585184322319)
            ·
              refine ⟨35688070086960877776483479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23792046724640585184322319 35688070086960877776483479)
              ·
                refine ⟨53532105130441316664725219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35688070086960877776483479 53532105130441316664725219)
                ·
                  refine ⟨80298157695661974997087829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53532105130441316664725219 80298157695661974997087829)
                  ·
                    refine ⟨940994035496038769497123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80298157695661974997087829 940994035496038769497123)
                    ·
                      rfl

theorem cell23_5497738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_5497738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497738 prefixEnd_5497738 := by exact prefixLift 5497738
  have htrace : WordTrace (prefixWord ++ tailWord_5497738) baseStart_5497738 baseEnd_5497738 := by
    simpa [prefixWord, tailWord_5497738, baseEnd_5497738] using wordTrace_append hprefix tailTrace_5497738
  have hstable : (prefixWord ++ tailWord_5497738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497738).length < 2 ^ (prefixWord ++ tailWord_5497738).sum := by decide
  have hdescent : baseEnd_5497738 < baseStart_5497738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497745 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 6, 2, 2]
def baseStart_5497745 : Nat := 118140960795 + 5497745 * 2 ^ 59
def prefixEnd_5497745 : Nat := 4983230072969 + 3 ^ 40 * 5497745 * 2
def baseEnd_5497745 : Nat := 2822985700852697781103837

theorem tailTrace_5497745 : CollatzResearch.WordTrace tailWord_5497745 prefixEnd_5497745 2822985700852697781103837 := by
  unfold tailWord_5497745
  simp only [CollatzResearch.WordTrace]
  refine ⟨200519233467616279938270689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133679488978410853292180459 200519233467616279938270689)
  ·
    refine ⟨150389425100712209953703017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200519233467616279938270689 150389425100712209953703017)
    ·
      refine ⟨112792068825534157465277263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150389425100712209953703017 112792068825534157465277263)
      ·
        refine ⟨169188103238301236197915895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112792068825534157465277263 169188103238301236197915895)
        ·
          refine ⟨253782154857451854296873843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169188103238301236197915895 253782154857451854296873843)
          ·
            refine ⟨380673232286177781445310765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253782154857451854296873843 380673232286177781445310765)
            ·
              refine ⟨142752462107316668041991537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380673232286177781445310765 142752462107316668041991537)
              ·
                refine ⟨107064346580487501031493653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142752462107316668041991537 107064346580487501031493653)
                ·
                  refine ⟨5018641245960351610851265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107064346580487501031493653 5018641245960351610851265)
                  ·
                    refine ⟨3763980934470263708138449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018641245960351610851265 3763980934470263708138449)
                    ·
                      refine ⟨2822985700852697781103837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763980934470263708138449 2822985700852697781103837)
                      ·
                        rfl

theorem cell23_5497745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_5497745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497745 prefixEnd_5497745 := by exact prefixLift 5497745
  have htrace : WordTrace (prefixWord ++ tailWord_5497745) baseStart_5497745 baseEnd_5497745 := by
    simpa [prefixWord, tailWord_5497745, baseEnd_5497745] using wordTrace_append hprefix tailTrace_5497745
  have hstable : (prefixWord ++ tailWord_5497745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497745).length < 2 ^ (prefixWord ++ tailWord_5497745).sum := by decide
  have hdescent : baseEnd_5497745 < baseStart_5497745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497762 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_5497762 : Nat := 118140960795 + 5497762 * 2 ^ 59
def prefixEnd_5497762 : Nat := 4983230072969 + 3 ^ 40 * 5497762 * 2
def baseEnd_5497762 : Nat := 2822994430023824214591259

theorem tailTrace_5497762 : CollatzResearch.WordTrace tailWord_5497762 prefixEnd_5497762 2822994430023824214591259 := by
  unfold tailWord_5497762
  simp only [CollatzResearch.WordTrace]
  refine ⟨50129963377138672960409885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133679902339036461227759693 50129963377138672960409885)
  ·
    refine ⟨18798736266427002360153707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50129963377138672960409885 18798736266427002360153707)
    ·
      refine ⟨28198104399640503540230561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18798736266427002360153707 28198104399640503540230561)
      ·
        refine ⟨21148578299730377655172921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28198104399640503540230561 21148578299730377655172921)
        ·
          refine ⟨15861433724797783241379691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21148578299730377655172921 15861433724797783241379691)
          ·
            refine ⟨23792150587196674862069537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15861433724797783241379691 23792150587196674862069537)
            ·
              refine ⟨17844112940397506146552153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23792150587196674862069537 17844112940397506146552153)
              ·
                refine ⟨13383084705298129609914115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17844112940397506146552153 13383084705298129609914115)
                ·
                  refine ⟨20074627057947194414871173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13383084705298129609914115 20074627057947194414871173)
                  ·
                    refine ⟨3763992573365098952788345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20074627057947194414871173 3763992573365098952788345)
                    ·
                      refine ⟨2822994430023824214591259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3763992573365098952788345 2822994430023824214591259)
                      ·
                        rfl

theorem cell23_5497762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_5497762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497762 prefixEnd_5497762 := by exact prefixLift 5497762
  have htrace : WordTrace (prefixWord ++ tailWord_5497762) baseStart_5497762 baseEnd_5497762 := by
    simpa [prefixWord, tailWord_5497762, baseEnd_5497762] using wordTrace_append hprefix tailTrace_5497762
  have hstable : (prefixWord ++ tailWord_5497762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497762).length < 2 ^ (prefixWord ++ tailWord_5497762).sum := by decide
  have hdescent : baseEnd_5497762 < baseStart_5497762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497773 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5497773 : Nat := 118140960795 + 5497773 * 2 ^ 59
def prefixEnd_5497773 : Nat := 4983230072969 + 3 ^ 40 * 5497773 * 2
def baseEnd_5497773 : Nat := 2823000078311023671553709

theorem tailTrace_5497773 : CollatzResearch.WordTrace tailWord_5497773 prefixEnd_5497773 2823000078311023671553709 := by
  unfold tailWord_5497773
  simp only [CollatzResearch.WordTrace]
  refine ⟨200520254711514840720289973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133680169807676560480193315 200520254711514840720289973)
  ·
    refine ⟨18798773879204516317527185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200520254711514840720289973 18798773879204516317527185)
    ·
      refine ⟨14099080409403387238145389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18798773879204516317527185 14099080409403387238145389)
      ·
        refine ⟨5287155153526270214304521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14099080409403387238145389 5287155153526270214304521)
        ·
          refine ⟨3965366365144702660728391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5287155153526270214304521 3965366365144702660728391)
          ·
            refine ⟨5948049547717053991092587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965366365144702660728391 5948049547717053991092587)
            ·
              refine ⟨8922074321575580986638881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948049547717053991092587 8922074321575580986638881)
              ·
                refine ⟨6691555741181685739979161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8922074321575580986638881 6691555741181685739979161)
                ·
                  refine ⟨5018666805886264304984371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6691555741181685739979161 5018666805886264304984371)
                  ·
                    refine ⟨7528000208829396457476557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5018666805886264304984371 7528000208829396457476557)
                    ·
                      refine ⟨2823000078311023671553709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7528000208829396457476557 2823000078311023671553709)
                      ·
                        rfl

theorem cell23_5497773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5497773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497773 prefixEnd_5497773 := by exact prefixLift 5497773
  have htrace : WordTrace (prefixWord ++ tailWord_5497773) baseStart_5497773 baseEnd_5497773 := by
    simpa [prefixWord, tailWord_5497773, baseEnd_5497773] using wordTrace_append hprefix tailTrace_5497773
  have hstable : (prefixWord ++ tailWord_5497773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497773).length < 2 ^ (prefixWord ++ tailWord_5497773).sum := by decide
  have hdescent : baseEnd_5497773 < baseStart_5497773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497785 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 5]
def baseStart_5497785 : Nat := 118140960795 + 5497785 * 2 ^ 59
def prefixEnd_5497785 : Nat := 4983230072969 + 3 ^ 40 * 5497785 * 2
def baseEnd_5497785 : Nat := 313667360008764180511517

theorem tailTrace_5497785 : CollatzResearch.WordTrace tailWord_5497785 prefixEnd_5497785 313667360008764180511517 := by
  unfold tailWord_5497785
  simp only [CollatzResearch.WordTrace]
  refine ⟨200520692387471366769726809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133680461591647577846484539 200520692387471366769726809)
  ·
    refine ⟨150390519290603525077295107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200520692387471366769726809 150390519290603525077295107)
    ·
      refine ⟨225585778935905287615942661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150390519290603525077295107 225585778935905287615942661)
      ·
        refine ⟨42297333550482241427989249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225585778935905287615942661 42297333550482241427989249)
        ·
          refine ⟨31723000162861681070991937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42297333550482241427989249 31723000162861681070991937)
          ·
            refine ⟨23792250122146260803243953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31723000162861681070991937 23792250122146260803243953)
            ·
              refine ⟨17844187591609695602432965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23792250122146260803243953 17844187591609695602432965)
              ·
                refine ⟨3345785173426817925456181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17844187591609695602432965 3345785173426817925456181)
                ·
                  refine ⟨313667360008764180511517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3345785173426817925456181 313667360008764180511517)
                  ·
                    rfl

theorem cell23_5497785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 5].length) (baseStart_5497785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497785 prefixEnd_5497785 := by exact prefixLift 5497785
  have htrace : WordTrace (prefixWord ++ tailWord_5497785) baseStart_5497785 baseEnd_5497785 := by
    simpa [prefixWord, tailWord_5497785, baseEnd_5497785] using wordTrace_append hprefix tailTrace_5497785
  have hstable : (prefixWord ++ tailWord_5497785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497785).length < 2 ^ (prefixWord ++ tailWord_5497785).sum := by decide
  have hdescent : baseEnd_5497785 < baseStart_5497785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497796 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5497796 : Nat := 118140960795 + 5497796 * 2 ^ 59
def prefixEnd_5497796 : Nat := 4983230072969 + 3 ^ 40 * 5497796 * 2
def baseEnd_5497796 : Nat := 2823011888366077081566103

theorem tailTrace_5497796 : CollatzResearch.WordTrace tailWord_5497796 prefixEnd_5497796 2823011888366077081566103 := by
  unfold tailWord_5497796
  simp only [CollatzResearch.WordTrace]
  refine ⟨100260546795215757824188621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133680729060287677098918161 100260546795215757824188621)
  ·
    refine ⟨37597705048205909184070733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100260546795215757824188621 37597705048205909184070733)
    ·
      refine ⟨14099139393077215944026525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37597705048205909184070733 14099139393077215944026525)
      ·
        refine ⟨5287177272403955979009947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14099139393077215944026525 5287177272403955979009947)
        ·
          refine ⟨7930765908605933968514921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287177272403955979009947 7930765908605933968514921)
          ·
            refine ⟨5948074431454450476386191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7930765908605933968514921 5948074431454450476386191)
            ·
              refine ⟨8922111647181675714579287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948074431454450476386191 8922111647181675714579287)
              ·
                refine ⟨13383167470772513571868931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8922111647181675714579287 13383167470772513571868931)
                ·
                  refine ⟨20074751206158770357803397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13383167470772513571868931 20074751206158770357803397)
                  ·
                    refine ⟨3764015851154769442088137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20074751206158770357803397 3764015851154769442088137)
                    ·
                      refine ⟨2823011888366077081566103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764015851154769442088137 2823011888366077081566103)
                      ·
                        rfl

theorem cell23_5497796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5497796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497796 prefixEnd_5497796 := by exact prefixLift 5497796
  have htrace : WordTrace (prefixWord ++ tailWord_5497796) baseStart_5497796 baseEnd_5497796 := by
    simpa [prefixWord, tailWord_5497796, baseEnd_5497796] using wordTrace_append hprefix tailTrace_5497796
  have hstable : (prefixWord ++ tailWord_5497796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497796).length < 2 ^ (prefixWord ++ tailWord_5497796).sum := by decide
  have hdescent : baseEnd_5497796 < baseStart_5497796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497842 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5497842 : Nat := 118140960795 + 5497842 * 2 ^ 59
def prefixEnd_5497842 : Nat := 4983230072969 + 3 ^ 40 * 5497842 * 2
def baseEnd_5497842 : Nat := 2823035508476183901590891

theorem tailTrace_5497842 : CollatzResearch.WordTrace tailWord_5497842 prefixEnd_5497842 2823035508476183901590891 := by
  unfold tailWord_5497842
  simp only [CollatzResearch.WordTrace]
  refine ⟨50130692837066216376137945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133681847565509910336367853 50130692837066216376137945)
  ·
    refine ⟨37598019627799662282103459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50130692837066216376137945 37598019627799662282103459)
    ·
      refine ⟨56397029441699493423155189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37598019627799662282103459 56397029441699493423155189)
      ·
        refine ⟨5287221510159327508420799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56397029441699493423155189 5287221510159327508420799)
        ·
          refine ⟨7930832265238991262631199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287221510159327508420799 7930832265238991262631199)
          ·
            refine ⟨11896248397858486893946799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7930832265238991262631199 11896248397858486893946799)
            ·
              refine ⟨17844372596787730340920199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11896248397858486893946799 17844372596787730340920199)
              ·
                refine ⟨26766558895181595511380299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17844372596787730340920199 26766558895181595511380299)
                ·
                  refine ⟨40149838342772393267070449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26766558895181595511380299 40149838342772393267070449)
                  ·
                    refine ⟨30112378757079294950302837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40149838342772393267070449 30112378757079294950302837)
                    ·
                      refine ⟨2823035508476183901590891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30112378757079294950302837 2823035508476183901590891)
                      ·
                        rfl

theorem cell23_5497842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5497842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497842 prefixEnd_5497842 := by exact prefixLift 5497842
  have htrace : WordTrace (prefixWord ++ tailWord_5497842) baseStart_5497842 baseEnd_5497842 := by
    simpa [prefixWord, tailWord_5497842, baseEnd_5497842] using wordTrace_append hprefix tailTrace_5497842
  have hstable : (prefixWord ++ tailWord_5497842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497842).length < 2 ^ (prefixWord ++ tailWord_5497842).sum := by decide
  have hdescent : baseEnd_5497842 < baseStart_5497842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497892 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 6]
def baseStart_5497892 : Nat := 118140960795 + 5497892 * 2 ^ 59
def prefixEnd_5497892 : Nat := 4983230072969 + 3 ^ 40 * 5497892 * 2
def baseEnd_5497892 : Nat := 313673464723212078440629

theorem tailTrace_5497892 : CollatzResearch.WordTrace tailWord_5497892 prefixEnd_5497892 313673464723212078440629 := by
  unfold tailWord_5497892
  simp only [CollatzResearch.WordTrace]
  refine ⟨100262297499041862021935965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133683063332055816029247953 100262297499041862021935965)
  ·
    refine ⟨37598361562140698258225987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100262297499041862021935965 37598361562140698258225987)
    ·
      refine ⟨56397542343211047387338981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37598361562140698258225987 56397542343211047387338981)
      ·
        refine ⟨10574539189352071385126059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56397542343211047387338981 10574539189352071385126059)
        ·
          refine ⟨15861808784028107077689089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10574539189352071385126059 15861808784028107077689089)
          ·
            refine ⟨11896356588021080308266817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15861808784028107077689089 11896356588021080308266817)
            ·
              refine ⟨8922267441015810231200113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11896356588021080308266817 8922267441015810231200113)
              ·
                refine ⟨6691700580761857673400085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8922267441015810231200113 6691700580761857673400085)
                ·
                  refine ⟨313673464723212078440629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6691700580761857673400085 313673464723212078440629)
                  ·
                    rfl

theorem cell23_5497892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_5497892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497892 prefixEnd_5497892 := by exact prefixLift 5497892
  have htrace : WordTrace (prefixWord ++ tailWord_5497892) baseStart_5497892 baseEnd_5497892 := by
    simpa [prefixWord, tailWord_5497892, baseEnd_5497892] using wordTrace_append hprefix tailTrace_5497892
  have hstable : (prefixWord ++ tailWord_5497892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497892).length < 2 ^ (prefixWord ++ tailWord_5497892).sum := by decide
  have hdescent : baseEnd_5497892 < baseStart_5497892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497925 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_5497925 : Nat := 118140960795 + 5497925 * 2 ^ 59
def prefixEnd_5497925 : Nat := 4983230072969 + 3 ^ 40 * 5497925 * 2
def baseEnd_5497925 : Nat := 2823078127370507076853009

theorem tailTrace_5497925 : CollatzResearch.WordTrace tailWord_5497925 prefixEnd_5497925 2823078127370507076853009 := by
  unfold tailWord_5497925
  simp only [CollatzResearch.WordTrace]
  refine ⟨200525798606964170679823229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133683865737976113786548819 200525798606964170679823229)
  ·
    refine ⟨75197174477611564004933711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200525798606964170679823229 75197174477611564004933711)
    ·
      refine ⟨112795761716417346007400567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75197174477611564004933711 112795761716417346007400567)
      ·
        refine ⟨169193642574626019011100851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112795761716417346007400567 169193642574626019011100851)
        ·
          refine ⟨253790463861939028516651277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169193642574626019011100851 253790463861939028516651277)
          ·
            refine ⟨95171423948227135693744229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253790463861939028516651277 95171423948227135693744229)
            ·
              refine ⟨17844641990292587942577043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95171423948227135693744229 17844641990292587942577043)
              ·
                refine ⟨26766962985438881913865565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17844641990292587942577043 26766962985438881913865565)
                ·
                  refine ⟨10037611119539580717699587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26766962985438881913865565 10037611119539580717699587)
                  ·
                    refine ⟨15056416679309371076549381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10037611119539580717699587 15056416679309371076549381)
                    ·
                      refine ⟨2823078127370507076853009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15056416679309371076549381 2823078127370507076853009)
                      ·
                        rfl

theorem cell23_5497925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_5497925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497925 prefixEnd_5497925 := by exact prefixLift 5497925
  have htrace : WordTrace (prefixWord ++ tailWord_5497925) baseStart_5497925 baseEnd_5497925 := by
    simpa [prefixWord, tailWord_5497925, baseEnd_5497925] using wordTrace_append hprefix tailTrace_5497925
  have hstable : (prefixWord ++ tailWord_5497925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497925).length < 2 ^ (prefixWord ++ tailWord_5497925).sum := by decide
  have hdescent : baseEnd_5497925 < baseStart_5497925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497945 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_5497945 : Nat := 118140960795 + 5497945 * 2 ^ 59
def prefixEnd_5497945 : Nat := 4983230072969 + 3 ^ 40 * 5497945 * 2
def baseEnd_5497945 : Nat := 2823088396983596998602917

theorem tailTrace_5497945 : CollatzResearch.WordTrace tailWord_5497945 prefixEnd_5497945 2823088396983596998602917 := by
  unfold tailWord_5497945
  simp only [CollatzResearch.WordTrace]
  refine ⟨200526528066891714095551289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133684352044594476063700859 200526528066891714095551289)
  ·
    refine ⟨150394896050168785571663467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200526528066891714095551289 150394896050168785571663467)
    ·
      refine ⟨225592344075253178357495201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150394896050168785571663467 225592344075253178357495201)
      ·
        refine ⟨169194258056439883768121401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225592344075253178357495201 169194258056439883768121401)
        ·
          refine ⟨126895693542329912826091051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169194258056439883768121401 126895693542329912826091051)
          ·
            refine ⟨190343540313494869239136577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126895693542329912826091051 190343540313494869239136577)
            ·
              refine ⟨142757655235121151929352433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190343540313494869239136577 142757655235121151929352433)
              ·
                refine ⟨107068241426340863947014325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142757655235121151929352433 107068241426340863947014325)
                ·
                  refine ⟨10037647633719455995032593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107068241426340863947014325 10037647633719455995032593)
                  ·
                    refine ⟨7528235725289591996274445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10037647633719455995032593 7528235725289591996274445)
                    ·
                      refine ⟨2823088396983596998602917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7528235725289591996274445 2823088396983596998602917)
                      ·
                        rfl

theorem cell23_5497945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_5497945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497945 prefixEnd_5497945 := by exact prefixLift 5497945
  have htrace : WordTrace (prefixWord ++ tailWord_5497945) baseStart_5497945 baseEnd_5497945 := by
    simpa [prefixWord, tailWord_5497945, baseEnd_5497945] using wordTrace_append hprefix tailTrace_5497945
  have hstable : (prefixWord ++ tailWord_5497945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497945).length < 2 ^ (prefixWord ++ tailWord_5497945).sum := by decide
  have hdescent : baseEnd_5497945 < baseStart_5497945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497959 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_5497959 : Nat := 118140960795 + 5497959 * 2 ^ 59
def prefixEnd_5497959 : Nat := 4983230072969 + 3 ^ 40 * 5497959 * 2
def baseEnd_5497959 : Nat := 2823095585712759943827853

theorem tailTrace_5497959 : CollatzResearch.WordTrace tailWord_5497959 prefixEnd_5497959 2823095585712759943827853 := by
  unfold tailWord_5497959
  simp only [CollatzResearch.WordTrace]
  refine ⟨200527038688840994486560931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133684692459227329657707287 200527038688840994486560931)
  ·
    refine ⟨300790558033261491729841397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200527038688840994486560931 300790558033261491729841397)
    ·
      refine ⟨28199114815618264849672631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 300790558033261491729841397 28199114815618264849672631)
      ·
        refine ⟨42298672223427397274508947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28199114815618264849672631 42298672223427397274508947)
        ·
          refine ⟨63448008335141095911763421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42298672223427397274508947 63448008335141095911763421)
          ·
            refine ⟨23793003125677910966911283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63448008335141095911763421 23793003125677910966911283)
            ·
              refine ⟨35689504688516866450366925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23793003125677910966911283 35689504688516866450366925)
              ·
                refine ⟨13383564258193824918887597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35689504688516866450366925 13383564258193824918887597)
                ·
                  refine ⟨5018836596822684344582849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13383564258193824918887597 5018836596822684344582849)
                  ·
                    refine ⟨3764127447617013258437137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018836596822684344582849 3764127447617013258437137)
                    ·
                      refine ⟨2823095585712759943827853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764127447617013258437137 2823095585712759943827853)
                      ·
                        rfl

theorem cell23_5497959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_5497959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497959 prefixEnd_5497959 := by exact prefixLift 5497959
  have htrace : WordTrace (prefixWord ++ tailWord_5497959) baseStart_5497959 baseEnd_5497959 := by
    simpa [prefixWord, tailWord_5497959, baseEnd_5497959] using wordTrace_append hprefix tailTrace_5497959
  have hstable : (prefixWord ++ tailWord_5497959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497959).length < 2 ^ (prefixWord ++ tailWord_5497959).sum := by decide
  have hdescent : baseEnd_5497959 < baseStart_5497959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497962 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_5497962 : Nat := 118140960795 + 5497962 * 2 ^ 59
def prefixEnd_5497962 : Nat := 4983230072969 + 3 ^ 40 * 5497962 * 2
def baseEnd_5497962 : Nat := 2823097126154723432090339

theorem tailTrace_5497962 : CollatzResearch.WordTrace tailWord_5497962 prefixEnd_5497962 2823097126154723432090339 := by
  unfold tailWord_5497962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50131787026957531499730035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133684765405220083999280093 50131787026957531499730035)
  ·
    refine ⟨75197680540436297249595053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50131787026957531499730035 75197680540436297249595053)
    ·
      refine ⟨28199130202663611468598145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75197680540436297249595053 28199130202663611468598145)
      ·
        refine ⟨21149347651997708601448609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28199130202663611468598145 21149347651997708601448609)
        ·
          refine ⟨15862010738998281451086457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21149347651997708601448609 15862010738998281451086457)
          ·
            refine ⟨11896508054248711088314843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15862010738998281451086457 11896508054248711088314843)
            ·
              refine ⟨17844762081373066632472265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11896508054248711088314843 17844762081373066632472265)
              ·
                refine ⟨13383571561029799974354199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17844762081373066632472265 13383571561029799974354199)
                ·
                  refine ⟨20075357341544699961531299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13383571561029799974354199 20075357341544699961531299)
                  ·
                    refine ⟨30113036012317049942296949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20075357341544699961531299 30113036012317049942296949)
                    ·
                      refine ⟨2823097126154723432090339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30113036012317049942296949 2823097126154723432090339)
                      ·
                        rfl

theorem cell23_5497962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_5497962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497962 prefixEnd_5497962 := by exact prefixLift 5497962
  have htrace : WordTrace (prefixWord ++ tailWord_5497962) baseStart_5497962 baseEnd_5497962 := by
    simpa [prefixWord, tailWord_5497962, baseEnd_5497962] using wordTrace_append hprefix tailTrace_5497962
  have hstable : (prefixWord ++ tailWord_5497962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497962).length < 2 ^ (prefixWord ++ tailWord_5497962).sum := by decide
  have hdescent : baseEnd_5497962 < baseStart_5497962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5497993 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 1, 2, 2]
def baseStart_5497993 : Nat := 118140960795 + 5497993 * 2 ^ 59
def prefixEnd_5497993 : Nat := 4983230072969 + 3 ^ 40 * 5497993 * 2
def baseEnd_5497993 : Nat := 2823113044055012810802697

theorem tailTrace_5497993 : CollatzResearch.WordTrace tailWord_5497993 prefixEnd_5497993 2823113044055012810802697 := by
  unfold tailWord_5497993
  simp only [CollatzResearch.WordTrace]
  refine ⟨200528278770717818293298633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133685519180478545528865755 200528278770717818293298633)
  ·
    refine ⟨150396209078038363719973975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200528278770717818293298633 150396209078038363719973975)
    ·
      refine ⟨225594313617057545579960963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150396209078038363719973975 225594313617057545579960963)
      ·
        refine ⟨338391470425586318369941445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225594313617057545579960963 338391470425586318369941445)
        ·
          refine ⟨63448400704797434694364021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 338391470425586318369941445 63448400704797434694364021)
          ·
            refine ⟨5948287566074759502596627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63448400704797434694364021 5948287566074759502596627)
            ·
              refine ⟨8922431349112139253894941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948287566074759502596627 8922431349112139253894941)
              ·
                refine ⟨3345911755917052220210603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8922431349112139253894941 3345911755917052220210603)
                ·
                  refine ⟨5018867633875578330315905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345911755917052220210603 5018867633875578330315905)
                  ·
                    refine ⟨3764150725406683747736929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018867633875578330315905 3764150725406683747736929)
                    ·
                      refine ⟨2823113044055012810802697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764150725406683747736929 2823113044055012810802697)
                      ·
                        rfl

theorem cell23_5497993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 2, 2].length) (baseStart_5497993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5497993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5497993 prefixEnd_5497993 := by exact prefixLift 5497993
  have htrace : WordTrace (prefixWord ++ tailWord_5497993) baseStart_5497993 baseEnd_5497993 := by
    simpa [prefixWord, tailWord_5497993, baseEnd_5497993] using wordTrace_append hprefix tailTrace_5497993
  have hstable : (prefixWord ++ tailWord_5497993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5497993).length < 2 ^ (prefixWord ++ tailWord_5497993).sum := by decide
  have hdescent : baseEnd_5497993 < baseStart_5497993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5497993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498010 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5498010 : Nat := 118140960795 + 5498010 * 2 ^ 59
def prefixEnd_5498010 : Nat := 4983230072969 + 3 ^ 40 * 5498010 * 2
def baseEnd_5498010 : Nat := 2823121773226139244290119

theorem tailTrace_5498010 : CollatzResearch.WordTrace tailWord_5498010 prefixEnd_5498010 2823121773226139244290119 := by
  unfold tailWord_5498010
  simp only [CollatzResearch.WordTrace]
  refine ⟨50132224702914057549166871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133685932541104153464444989 50132224702914057549166871)
  ·
    refine ⟨75198337054371086323750307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50132224702914057549166871 75198337054371086323750307)
    ·
      refine ⟨112797505581556629485625461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75198337054371086323750307 112797505581556629485625461)
      ·
        refine ⟨10574766148270934014277387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112797505581556629485625461 10574766148270934014277387)
        ·
          refine ⟨15862149222406401021416081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10574766148270934014277387 15862149222406401021416081)
          ·
            refine ⟨11896611916804800766062061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15862149222406401021416081 11896611916804800766062061)
            ·
              refine ⟨4461229468801800287273273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11896611916804800766062061 4461229468801800287273273)
              ·
                refine ⟨3345922101601350215454955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461229468801800287273273 3345922101601350215454955)
                ·
                  refine ⟨5018883152402025323182433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345922101601350215454955 5018883152402025323182433)
                  ·
                    refine ⟨3764162364301518992386825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018883152402025323182433 3764162364301518992386825)
                    ·
                      refine ⟨2823121773226139244290119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764162364301518992386825 2823121773226139244290119)
                      ·
                        rfl

theorem cell23_5498010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5498010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498010 prefixEnd_5498010 := by exact prefixLift 5498010
  have htrace : WordTrace (prefixWord ++ tailWord_5498010) baseStart_5498010 baseEnd_5498010 := by
    simpa [prefixWord, tailWord_5498010, baseEnd_5498010] using wordTrace_append hprefix tailTrace_5498010
  have hstable : (prefixWord ++ tailWord_5498010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498010).length < 2 ^ (prefixWord ++ tailWord_5498010).sum := by decide
  have hdescent : baseEnd_5498010 < baseStart_5498010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498035 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5]
def baseStart_5498035 : Nat := 118140960795 + 5498035 * 2 ^ 59
def prefixEnd_5498035 : Nat := 4983230072969 + 3 ^ 40 * 5498035 * 2
def baseEnd_5498035 : Nat := 2823134610242501646477503

theorem tailTrace_5498035 : CollatzResearch.WordTrace tailWord_5498035 prefixEnd_5498035 2823134610242501646477503 := by
  unfold tailWord_5498035
  simp only [CollatzResearch.WordTrace]
  refine ⟨200529810636565659466327559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133686540424377106310885039 200529810636565659466327559)
  ·
    refine ⟨300794715954848489199491339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200529810636565659466327559 300794715954848489199491339)
    ·
      refine ⟨451192073932272733799237009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300794715954848489199491339 451192073932272733799237009)
      ·
        refine ⟨338394055449204550349427757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451192073932272733799237009 338394055449204550349427757)
        ·
          refine ⟨126897770793451706381035409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338394055449204550349427757 126897770793451706381035409)
          ·
            refine ⟨95173328095088779785776557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126897770793451706381035409 95173328095088779785776557)
            ·
              refine ⟨35689998035658292419666209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95173328095088779785776557 35689998035658292419666209)
              ·
                refine ⟨26767498526743719314749657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35689998035658292419666209 26767498526743719314749657)
                ·
                  refine ⟨20075623895057789486062243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26767498526743719314749657 20075623895057789486062243)
                  ·
                    refine ⟨30113435842586684229093365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20075623895057789486062243 30113435842586684229093365)
                    ·
                      refine ⟨2823134610242501646477503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30113435842586684229093365 2823134610242501646477503)
                      ·
                        rfl

theorem cell23_5498035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_5498035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498035 prefixEnd_5498035 := by exact prefixLift 5498035
  have htrace : WordTrace (prefixWord ++ tailWord_5498035) baseStart_5498035 baseEnd_5498035 := by
    simpa [prefixWord, tailWord_5498035, baseEnd_5498035] using wordTrace_append hprefix tailTrace_5498035
  have hstable : (prefixWord ++ tailWord_5498035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498035).length < 2 ^ (prefixWord ++ tailWord_5498035).sum := by decide
  have hdescent : baseEnd_5498035 < baseStart_5498035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498061 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5498061 : Nat := 118140960795 + 5498061 * 2 ^ 59
def prefixEnd_5498061 : Nat := 4983230072969 + 3 ^ 40 * 5498061 * 2
def baseEnd_5498061 : Nat := 2823147960739518544752385

theorem tailTrace_5498061 : CollatzResearch.WordTrace tailWord_5498061 prefixEnd_5498061 2823147960739518544752385 := by
  unfold tailWord_5498061
  simp only [CollatzResearch.WordTrace]
  refine ⟨200530758934471465906774037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133687172622980977271182691 200530758934471465906774037)
  ·
    refine ⟨9399879325053349964380033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200530758934471465906774037 9399879325053349964380033)
    ·
      refine ⟨7049909493790012473285025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9399879325053349964380033 7049909493790012473285025)
      ·
        refine ⟨5287432120342509354963769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7049909493790012473285025 5287432120342509354963769)
        ·
          refine ⟨3965574090256882016222827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5287432120342509354963769 3965574090256882016222827)
          ·
            refine ⟨5948361135385323024334241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965574090256882016222827 5948361135385323024334241)
            ·
              refine ⟨4461270851538992268250681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5948361135385323024334241 4461270851538992268250681)
              ·
                refine ⟨3345953138654244201188011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461270851538992268250681 3345953138654244201188011)
                ·
                  refine ⟨5018929707981366301782017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345953138654244201188011 5018929707981366301782017)
                  ·
                    refine ⟨3764197280986024726336513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5018929707981366301782017 3764197280986024726336513)
                    ·
                      refine ⟨2823147960739518544752385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764197280986024726336513 2823147960739518544752385)
                      ·
                        rfl

theorem cell23_5498061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5498061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498061 prefixEnd_5498061 := by exact prefixLift 5498061
  have htrace : WordTrace (prefixWord ++ tailWord_5498061) baseStart_5498061 baseEnd_5498061 := by
    simpa [prefixWord, tailWord_5498061, baseEnd_5498061] using wordTrace_append hprefix tailTrace_5498061
  have hstable : (prefixWord ++ tailWord_5498061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498061).length < 2 ^ (prefixWord ++ tailWord_5498061).sum := by decide
  have hdescent : baseEnd_5498061 < baseStart_5498061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498122 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_5498122 : Nat := 118140960795 + 5498122 * 2 ^ 59
def prefixEnd_5498122 : Nat := 4983230072969 + 3 ^ 40 * 5498122 * 2
def baseEnd_5498122 : Nat := 2823179283059442806089603

theorem tailTrace_5498122 : CollatzResearch.WordTrace tailWord_5498122 prefixEnd_5498122 2823179283059442806089603 := by
  unfold tailWord_5498122
  simp only [CollatzResearch.WordTrace]
  refine ⟨50133245946812618331186155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133688655858166982216496413 50133245946812618331186155)
  ·
    refine ⟨75199868920218927496779233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50133245946812618331186155 75199868920218927496779233)
    ·
      refine ⟨56399901690164195622584425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75199868920218927496779233 56399901690164195622584425)
      ·
        refine ⟨42299926267623146716938319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56399901690164195622584425 42299926267623146716938319)
        ·
          refine ⟨63449889401434720075407479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42299926267623146716938319 63449889401434720075407479)
          ·
            refine ⟨95174834102152080113111219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63449889401434720075407479 95174834102152080113111219)
            ·
              refine ⟨142762251153228120169666829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95174834102152080113111219 142762251153228120169666829)
              ·
                refine ⟨53535844182460545063625061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142762251153228120169666829 53535844182460545063625061)
                ·
                  refine ⟨10037970784211352199429699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53535844182460545063625061 10037970784211352199429699)
                  ·
                    refine ⟨15056956176317028299144549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10037970784211352199429699 15056956176317028299144549)
                    ·
                      refine ⟨2823179283059442806089603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15056956176317028299144549 2823179283059442806089603)
                      ·
                        rfl

theorem cell23_5498122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_5498122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498122 prefixEnd_5498122 := by exact prefixLift 5498122
  have htrace : WordTrace (prefixWord ++ tailWord_5498122) baseStart_5498122 baseEnd_5498122 := by
    simpa [prefixWord, tailWord_5498122, baseEnd_5498122] using wordTrace_append hprefix tailTrace_5498122
  have hstable : (prefixWord ++ tailWord_5498122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498122).length < 2 ^ (prefixWord ++ tailWord_5498122).sum := by decide
  have hdescent : baseEnd_5498122 < baseStart_5498122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498149 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_5498149 : Nat := 118140960795 + 5498149 * 2 ^ 59
def prefixEnd_5498149 : Nat := 4983230072969 + 3 ^ 40 * 5498149 * 2
def baseEnd_5498149 : Nat := 941064382345704733483993

theorem tailTrace_5498149 : CollatzResearch.WordTrace tailWord_5498149 prefixEnd_5498149 941064382345704733483993 := by
  unfold tailWord_5498149
  simp only [CollatzResearch.WordTrace]
  refine ⟨200533968558152656935977501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133689312372101771290651667 200533968558152656935977501)
  ·
    refine ⟨75200238209307246350991563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200533968558152656935977501 75200238209307246350991563)
    ·
      refine ⟨112800357313960869526487345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75200238209307246350991563 112800357313960869526487345)
      ·
        refine ⟨84600267985470652144865509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112800357313960869526487345 84600267985470652144865509)
        ·
          refine ⟨15862550247275747277162283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84600267985470652144865509 15862550247275747277162283)
          ·
            refine ⟨23793825370913620915743425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15862550247275747277162283 23793825370913620915743425)
            ·
              refine ⟨17845369028185215686807569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23793825370913620915743425 17845369028185215686807569)
              ·
                refine ⟨13384026771138911765105677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17845369028185215686807569 13384026771138911765105677)
                ·
                  refine ⟨5019010039177091911914629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13384026771138911765105677 5019010039177091911914629)
                  ·
                    refine ⟨941064382345704733483993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019010039177091911914629 941064382345704733483993)
                    ·
                      rfl

theorem cell23_5498149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_5498149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498149 prefixEnd_5498149 := by exact prefixLift 5498149
  have htrace : WordTrace (prefixWord ++ tailWord_5498149) baseStart_5498149 baseEnd_5498149 := by
    simpa [prefixWord, tailWord_5498149, baseEnd_5498149] using wordTrace_append hprefix tailTrace_5498149
  have hstable : (prefixWord ++ tailWord_5498149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498149).length < 2 ^ (prefixWord ++ tailWord_5498149).sum := by decide
  have hdescent : baseEnd_5498149 < baseStart_5498149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498162 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_5498162 : Nat := 118140960795 + 5498162 * 2 ^ 59
def prefixEnd_5498162 : Nat := 4983230072969 + 3 ^ 40 * 5498162 * 2
def baseEnd_5498162 : Nat := 313688869142846961065491

theorem tailTrace_5498162 : CollatzResearch.WordTrace tailWord_5498162 prefixEnd_5498162 313688869142846961065491 := by
  unfold tailWord_5498162
  simp only [CollatzResearch.WordTrace]
  refine ⟨50133610676776390039050185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133689628471403706770800493 50133610676776390039050185)
  ·
    refine ⟨37600208007582292529287639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50133610676776390039050185 37600208007582292529287639)
    ·
      refine ⟨56400312011373438793931459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37600208007582292529287639 56400312011373438793931459)
      ·
        refine ⟨84600468017060158190897189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56400312011373438793931459 84600468017060158190897189)
        ·
          refine ⟨15862587753198779660793223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84600468017060158190897189 15862587753198779660793223)
          ·
            refine ⟨23793881629798169491189835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15862587753198779660793223 23793881629798169491189835)
            ·
              refine ⟨35690822444697254236784753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23793881629798169491189835 35690822444697254236784753)
              ·
                refine ⟨26768116833522940677588565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35690822444697254236784753 26768116833522940677588565)
                ·
                  refine ⟨313688869142846961065491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26768116833522940677588565 313688869142846961065491)
                  ·
                    rfl

theorem cell23_5498162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_5498162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498162 prefixEnd_5498162 := by exact prefixLift 5498162
  have htrace : WordTrace (prefixWord ++ tailWord_5498162) baseStart_5498162 baseEnd_5498162 := by
    simpa [prefixWord, tailWord_5498162, baseEnd_5498162] using wordTrace_append hprefix tailTrace_5498162
  have hstable : (prefixWord ++ tailWord_5498162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498162).length < 2 ^ (prefixWord ++ tailWord_5498162).sum := by decide
  have hdescent : baseEnd_5498162 < baseStart_5498162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498183 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 1, 4]
def baseStart_5498183 : Nat := 118140960795 + 5498183 * 2 ^ 59
def prefixEnd_5498183 : Nat := 4983230072969 + 3 ^ 40 * 5498183 * 2
def baseEnd_5498183 : Nat := 941070201793122355808941

theorem tailTrace_5498183 : CollatzResearch.WordTrace tailWord_5498183 prefixEnd_5498183 941070201793122355808941 := by
  unfold tailWord_5498183
  simp only [CollatzResearch.WordTrace]
  refine ⟨200535208640029480742715203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133690139093352987161810135 200535208640029480742715203)
  ·
    refine ⟨300802812960044221114072805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200535208640029480742715203 300802812960044221114072805)
    ·
      refine ⟨56400527430008291458888651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300802812960044221114072805 56400527430008291458888651)
      ·
        refine ⟨84600791145012437188332977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56400527430008291458888651 84600791145012437188332977)
        ·
          refine ⟨63450593358759327891249733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84600791145012437188332977 63450593358759327891249733)
          ·
            refine ⟨11896986254767373979609325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63450593358759327891249733 11896986254767373979609325)
            ·
              refine ⟨4461369845537765242353497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11896986254767373979609325 4461369845537765242353497)
              ·
                refine ⟨3346027384153323931765123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4461369845537765242353497 3346027384153323931765123)
                ·
                  refine ⟨5019041076229985897647685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346027384153323931765123 5019041076229985897647685)
                  ·
                    refine ⟨941070201793122355808941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019041076229985897647685 941070201793122355808941)
                    ·
                      rfl

theorem cell23_5498183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_5498183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498183 prefixEnd_5498183 := by exact prefixLift 5498183
  have htrace : WordTrace (prefixWord ++ tailWord_5498183) baseStart_5498183 baseEnd_5498183 := by
    simpa [prefixWord, tailWord_5498183, baseEnd_5498183] using wordTrace_append hprefix tailTrace_5498183
  have hstable : (prefixWord ++ tailWord_5498183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498183).length < 2 ^ (prefixWord ++ tailWord_5498183).sum := by decide
  have hdescent : baseEnd_5498183 < baseStart_5498183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498192 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_5498192 : Nat := 118140960795 + 5498192 * 2 ^ 59
def prefixEnd_5498192 : Nat := 4983230072969 + 3 ^ 40 * 5498192 * 2
def baseEnd_5498192 : Nat := 941071742235085844071427

theorem tailTrace_5498192 : CollatzResearch.WordTrace tailWord_5498192 prefixEnd_5498192 941071742235085844071427 := by
  unfold tailWord_5498192
  simp only [CollatzResearch.WordTrace]
  refine ⟨100267768448498437639896415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133690357931331250186528553 100267768448498437639896415)
  ·
    refine ⟨150401652672747656459844623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100267768448498437639896415 150401652672747656459844623)
    ·
      refine ⟨225602479009121484689766935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150401652672747656459844623 225602479009121484689766935)
      ·
        refine ⟨338403718513682227034650403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225602479009121484689766935 338403718513682227034650403)
        ·
          refine ⟨507605577770523340551975605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338403718513682227034650403 507605577770523340551975605)
          ·
            refine ⟨47588022915986563176747713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 507605577770523340551975605 47588022915986563176747713)
            ·
              refine ⟨35691017186989922382560785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47588022915986563176747713 35691017186989922382560785)
              ·
                refine ⟨26768262890242441786920589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35691017186989922382560785 26768262890242441786920589)
                ·
                  refine ⟨10038098583840915670095221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26768262890242441786920589 10038098583840915670095221)
                  ·
                    refine ⟨941071742235085844071427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10038098583840915670095221 941071742235085844071427)
                    ·
                      rfl

theorem cell23_5498192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_5498192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498192 prefixEnd_5498192 := by exact prefixLift 5498192
  have htrace : WordTrace (prefixWord ++ tailWord_5498192) baseStart_5498192 baseEnd_5498192 := by
    simpa [prefixWord, tailWord_5498192, baseEnd_5498192] using wordTrace_append hprefix tailTrace_5498192
  have hstable : (prefixWord ++ tailWord_5498192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498192).length < 2 ^ (prefixWord ++ tailWord_5498192).sum := by decide
  have hdescent : baseEnd_5498192 < baseStart_5498192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498226 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_5498226 : Nat := 118140960795 + 5498226 * 2 ^ 59
def prefixEnd_5498226 : Nat := 4983230072969 + 3 ^ 40 * 5498226 * 2
def baseEnd_5498226 : Nat := 941077561682503466396375

theorem tailTrace_5498226 : CollatzResearch.WordTrace tailWord_5498226 prefixEnd_5498226 941077561682503466396375 := by
  unfold tailWord_5498226
  simp only [CollatzResearch.WordTrace]
  refine ⟨50134194244718424771632633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133691184652582466057687021 50134194244718424771632633)
  ·
    refine ⟨37600645683538818578724475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50134194244718424771632633 37600645683538818578724475)
    ·
      refine ⟨56400968525308227868086713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37600645683538818578724475 56400968525308227868086713)
      ·
        refine ⟨42300726393981170901065035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56400968525308227868086713 42300726393981170901065035)
        ·
          refine ⟨63451089590971756351597553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42300726393981170901065035 63451089590971756351597553)
          ·
            refine ⟨47588317193228817263698165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63451089590971756351597553 47588317193228817263698165)
            ·
              refine ⟨4461404736865201618471703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47588317193228817263698165 4461404736865201618471703)
              ·
                refine ⟨6692107105297802427707555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4461404736865201618471703 6692107105297802427707555)
                ·
                  refine ⟨10038160657946703641561333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6692107105297802427707555 10038160657946703641561333)
                  ·
                    refine ⟨941077561682503466396375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10038160657946703641561333 941077561682503466396375)
                    ·
                      rfl

theorem cell23_5498226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_5498226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498226 prefixEnd_5498226 := by exact prefixLift 5498226
  have htrace : WordTrace (prefixWord ++ tailWord_5498226) baseStart_5498226 baseEnd_5498226 := by
    simpa [prefixWord, tailWord_5498226, baseEnd_5498226] using wordTrace_append hprefix tailTrace_5498226
  have hstable : (prefixWord ++ tailWord_5498226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498226).length < 2 ^ (prefixWord ++ tailWord_5498226).sum := by decide
  have hdescent : baseEnd_5498226 < baseStart_5498226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498266 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_5498266 : Nat := 118140960795 + 5498266 * 2 ^ 59
def prefixEnd_5498266 : Nat := 4983230072969 + 3 ^ 40 * 5498266 * 2
def baseEnd_5498266 : Nat := 2823253224273690242688941

theorem tailTrace_5498266 : CollatzResearch.WordTrace tailWord_5498266 prefixEnd_5498266 2823253224273690242688941 := by
  unfold tailWord_5498266
  simp only [CollatzResearch.WordTrace]
  refine ⟨50134558974682196479496663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133692157265819190611991101 50134558974682196479496663)
  ·
    refine ⟨75201838462023294719244995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50134558974682196479496663 75201838462023294719244995)
    ·
      refine ⟨112802757693034942078867493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75201838462023294719244995 112802757693034942078867493)
      ·
        refine ⟨21150517067444051639787655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112802757693034942078867493 21150517067444051639787655)
        ·
          refine ⟨31725775601166077459681483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21150517067444051639787655 31725775601166077459681483)
          ·
            refine ⟨47588663401749116189522225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31725775601166077459681483 47588663401749116189522225)
            ·
              refine ⟨35691497551311837142141669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47588663401749116189522225 35691497551311837142141669)
              ·
                refine ⟨6692155790870969464151563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35691497551311837142141669 6692155790870969464151563)
                ·
                  refine ⟨10038233686306454196227345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6692155790870969464151563 10038233686306454196227345)
                  ·
                    refine ⟨7528675264729840647170509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10038233686306454196227345 7528675264729840647170509)
                    ·
                      refine ⟨2823253224273690242688941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7528675264729840647170509 2823253224273690242688941)
                      ·
                        rfl

theorem cell23_5498266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_5498266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498266 prefixEnd_5498266 := by exact prefixLift 5498266
  have htrace : WordTrace (prefixWord ++ tailWord_5498266) baseStart_5498266 baseEnd_5498266 := by
    simpa [prefixWord, tailWord_5498266, baseEnd_5498266] using wordTrace_append hprefix tailTrace_5498266
  have hstable : (prefixWord ++ tailWord_5498266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498266).length < 2 ^ (prefixWord ++ tailWord_5498266).sum := by decide
  have hdescent : baseEnd_5498266 < baseStart_5498266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498326 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5498326 : Nat := 118140960795 + 5498326 * 2 ^ 59
def prefixEnd_5498326 : Nat := 4983230072969 + 3 ^ 40 * 5498326 * 2
def baseEnd_5498326 : Nat := 2823284033112960007938665

theorem tailTrace_5498326 : CollatzResearch.WordTrace tailWord_5498326 prefixEnd_5498326 2823284033112960007938665 := by
  unfold tailWord_5498326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533776517406963510323177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133693616185674277443447221 12533776517406963510323177)
  ·
    refine ⟨9400332388055222632742383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12533776517406963510323177 9400332388055222632742383)
    ·
      refine ⟨14100498582082833949113575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9400332388055222632742383 14100498582082833949113575)
      ·
        refine ⟨21150747873124250923670363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14100498582082833949113575 21150747873124250923670363)
        ·
          refine ⟨31726121809686376385505545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21150747873124250923670363 31726121809686376385505545)
          ·
            refine ⟨23794591357264782289129159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31726121809686376385505545 23794591357264782289129159)
            ·
              refine ⟨35691887035897173433693739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23794591357264782289129159 35691887035897173433693739)
              ·
                refine ⟨53537830553845760150540609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35691887035897173433693739 53537830553845760150540609)
                ·
                  refine ⟨40153372915384320112905457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53537830553845760150540609 40153372915384320112905457)
                  ·
                    refine ⟨30115029686538240084679093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40153372915384320112905457 30115029686538240084679093)
                    ·
                      refine ⟨2823284033112960007938665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30115029686538240084679093 2823284033112960007938665)
                      ·
                        rfl

theorem cell23_5498326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5498326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498326 prefixEnd_5498326 := by exact prefixLift 5498326
  have htrace : WordTrace (prefixWord ++ tailWord_5498326) baseStart_5498326 baseEnd_5498326 := by
    simpa [prefixWord, tailWord_5498326, baseEnd_5498326] using wordTrace_append hprefix tailTrace_5498326
  have hstable : (prefixWord ++ tailWord_5498326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498326).length < 2 ^ (prefixWord ++ tailWord_5498326).sum := by decide
  have hdescent : baseEnd_5498326 < baseStart_5498326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498339 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5498339 : Nat := 118140960795 + 5498339 * 2 ^ 59
def prefixEnd_5498339 : Nat := 4983230072969 + 3 ^ 40 * 5498339 * 2
def baseEnd_5498339 : Nat := 2823290708361468457076105

theorem tailTrace_5498339 : CollatzResearch.WordTrace tailWord_5498339 prefixEnd_5498339 2823290708361468457076105 := by
  unfold tailWord_5498339
  simp only [CollatzResearch.WordTrace]
  refine ⟨200540898427464319385394071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133693932284976212923596047 200540898427464319385394071)
  ·
    refine ⟨300811347641196479078091107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200540898427464319385394071 300811347641196479078091107)
    ·
      refine ⟨451217021461794718617136661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300811347641196479078091107 451217021461794718617136661)
      ·
        refine ⟨21150797881021627435178281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 451217021461794718617136661 21150797881021627435178281)
        ·
          refine ⟨15863098410766220576383711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21150797881021627435178281 15863098410766220576383711)
          ·
            refine ⟨23794647616149330864575567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15863098410766220576383711 23794647616149330864575567)
            ·
              refine ⟨35691971424223996296863351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23794647616149330864575567 35691971424223996296863351)
              ·
                refine ⟨53537957136335994445295027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35691971424223996296863351 53537957136335994445295027)
                ·
                  refine ⟨80306935704503991667942541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53537957136335994445295027 80306935704503991667942541)
                  ·
                    refine ⟨30115100889188996875478453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80306935704503991667942541 30115100889188996875478453)
                    ·
                      refine ⟨2823290708361468457076105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30115100889188996875478453 2823290708361468457076105)
                      ·
                        rfl

theorem cell23_5498339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5498339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498339 prefixEnd_5498339 := by exact prefixLift 5498339
  have htrace : WordTrace (prefixWord ++ tailWord_5498339) baseStart_5498339 baseEnd_5498339 := by
    simpa [prefixWord, tailWord_5498339, baseEnd_5498339] using wordTrace_append hprefix tailTrace_5498339
  have hstable : (prefixWord ++ tailWord_5498339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498339).length < 2 ^ (prefixWord ++ tailWord_5498339).sum := by decide
  have hdescent : baseEnd_5498339 < baseStart_5498339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498353 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 4, 2, 2]
def baseStart_5498353 : Nat := 118140960795 + 5498353 * 2 ^ 59
def prefixEnd_5498353 : Nat := 4983230072969 + 3 ^ 40 * 5498353 * 2
def baseEnd_5498353 : Nat := 2823297897090631402301041

theorem tailTrace_5498353 : CollatzResearch.WordTrace tailWord_5498353 prefixEnd_5498353 2823297897090631402301041 := by
  unfold tailWord_5498353
  simp only [CollatzResearch.WordTrace]
  refine ⟨200541409049413599776403713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133694272699609066517602475 200541409049413599776403713)
  ·
    refine ⟨150406056787060199832302785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200541409049413599776403713 150406056787060199832302785)
    ·
      refine ⟨112804542590295149874227089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150406056787060199832302785 112804542590295149874227089)
      ·
        refine ⟨84603406942721362405670317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112804542590295149874227089 84603406942721362405670317)
        ·
          refine ⟨31726277603520510902126369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84603406942721362405670317 31726277603520510902126369)
          ·
            refine ⟨23794708202640383176594777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31726277603520510902126369 23794708202640383176594777)
            ·
              refine ⟨17846031151980287382446083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23794708202640383176594777 17846031151980287382446083)
              ·
                refine ⟨26769046727970431073669125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17846031151980287382446083 26769046727970431073669125)
                ·
                  refine ⟨5019196261494455826312961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26769046727970431073669125 5019196261494455826312961)
                  ·
                    refine ⟨3764397196120841869734721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5019196261494455826312961 3764397196120841869734721)
                    ·
                      refine ⟨2823297897090631402301041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764397196120841869734721 2823297897090631402301041)
                      ·
                        rfl

theorem cell23_5498353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_5498353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498353 prefixEnd_5498353 := by exact prefixLift 5498353
  have htrace : WordTrace (prefixWord ++ tailWord_5498353) baseStart_5498353 baseEnd_5498353 := by
    simpa [prefixWord, tailWord_5498353, baseEnd_5498353] using wordTrace_append hprefix tailTrace_5498353
  have hstable : (prefixWord ++ tailWord_5498353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498353).length < 2 ^ (prefixWord ++ tailWord_5498353).sum := by decide
  have hdescent : baseEnd_5498353 < baseStart_5498353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498374 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5498374 : Nat := 118140960795 + 5498374 * 2 ^ 59
def prefixEnd_5498374 : Nat := 4983230072969 + 3 ^ 40 * 5498374 * 2
def baseEnd_5498374 : Nat := 2823308680184375820138445

theorem tailTrace_5498374 : CollatzResearch.WordTrace tailWord_5498374 prefixEnd_5498374 2823308680184375820138445 := by
  unfold tailWord_5498374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266942968198047511341193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133694783321558346908612117 6266942968198047511341193)
  ·
    refine ⟨4700207226148535633505895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6266942968198047511341193 4700207226148535633505895)
    ·
      refine ⟨7050310839222803450258843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700207226148535633505895 7050310839222803450258843)
      ·
        refine ⟨10575466258834205175388265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050310839222803450258843 10575466258834205175388265)
        ·
          refine ⟨7931599694125653881541199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10575466258834205175388265 7931599694125653881541199)
          ·
            refine ⟨11897399541188480822311799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7931599694125653881541199 11897399541188480822311799)
            ·
              refine ⟨17846099311782721233467699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11897399541188480822311799 17846099311782721233467699)
              ·
                refine ⟨26769148967674081850201549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17846099311782721233467699 26769148967674081850201549)
                ·
                  refine ⟨10038430862877780693825581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26769148967674081850201549 10038430862877780693825581)
                  ·
                    refine ⟨3764411573579167760184593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10038430862877780693825581 3764411573579167760184593)
                    ·
                      refine ⟨2823308680184375820138445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764411573579167760184593 2823308680184375820138445)
                      ·
                        rfl

theorem cell23_5498374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5498374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498374 prefixEnd_5498374 := by exact prefixLift 5498374
  have htrace : WordTrace (prefixWord ++ tailWord_5498374) baseStart_5498374 baseEnd_5498374 := by
    simpa [prefixWord, tailWord_5498374, baseEnd_5498374] using wordTrace_append hprefix tailTrace_5498374
  have hstable : (prefixWord ++ tailWord_5498374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498374).length < 2 ^ (prefixWord ++ tailWord_5498374).sum := by decide
  have hdescent : baseEnd_5498374 < baseStart_5498374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498399 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_5498399 : Nat := 118140960795 + 5498399 * 2 ^ 59
def prefixEnd_5498399 : Nat := 4983230072969 + 3 ^ 40 * 5498399 * 2
def baseEnd_5498399 : Nat := 2823321517200738222325829

theorem tailTrace_5498399 : CollatzResearch.WordTrace tailWord_5498399 prefixEnd_5498399 2823321517200738222325829 := by
  unfold tailWord_5498399
  simp only [CollatzResearch.WordTrace]
  refine ⟨200543086807246949632578251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133695391204831299755052167 200543086807246949632578251)
  ·
    refine ⟨300814630210870424448867377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200543086807246949632578251 300814630210870424448867377)
    ·
      refine ⟨225610972658152818336650533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300814630210870424448867377 225610972658152818336650533)
      ·
        refine ⟨42302057373403653438121975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225610972658152818336650533 42302057373403653438121975)
        ·
          refine ⟨63453086060105480157182963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42302057373403653438121975 63453086060105480157182963)
          ·
            refine ⟨95179629090158220235774445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63453086060105480157182963 95179629090158220235774445)
            ·
              refine ⟨35692360908809332588415417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95179629090158220235774445 35692360908809332588415417)
              ·
                refine ⟨26769270681606999441311563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35692360908809332588415417 26769270681606999441311563)
                ·
                  refine ⟨40153906022410499161967345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26769270681606999441311563 40153906022410499161967345)
                  ·
                    refine ⟨30115429516807874371475509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40153906022410499161967345 30115429516807874371475509)
                    ·
                      refine ⟨2823321517200738222325829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30115429516807874371475509 2823321517200738222325829)
                      ·
                        rfl

theorem cell23_5498399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_5498399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498399 prefixEnd_5498399 := by exact prefixLift 5498399
  have htrace : WordTrace (prefixWord ++ tailWord_5498399) baseStart_5498399 baseEnd_5498399 := by
    simpa [prefixWord, tailWord_5498399, baseEnd_5498399] using wordTrace_append hprefix tailTrace_5498399
  have hstable : (prefixWord ++ tailWord_5498399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498399).length < 2 ^ (prefixWord ++ tailWord_5498399).sum := by decide
  have hdescent : baseEnd_5498399 < baseStart_5498399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498449 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 8]
def baseStart_5498449 : Nat := 118140960795 + 5498449 * 2 ^ 59
def prefixEnd_5498449 : Nat := 4983230072969 + 3 ^ 40 * 5498449 * 2
def baseEnd_5498449 : Nat := 313705243470384780744511

theorem tailTrace_5498449 : CollatzResearch.WordTrace tailWord_5498449 prefixEnd_5498449 313705243470384780744511 := by
  unfold tailWord_5498449
  simp only [CollatzResearch.WordTrace]
  refine ⟨200544910457065808171898401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133696606971377205447932267 200544910457065808171898401)
  ·
    refine ⟨150408682842799356128923801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200544910457065808171898401 150408682842799356128923801)
    ·
      refine ⟨112806512132099517096692851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150408682842799356128923801 112806512132099517096692851)
      ·
        refine ⟨169209768198149275645039277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112806512132099517096692851 169209768198149275645039277)
        ·
          refine ⟨63453663074305978366889729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169209768198149275645039277 63453663074305978366889729)
          ·
            refine ⟨47590247305729483775167297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63453663074305978366889729 47590247305729483775167297)
            ·
              refine ⟨35692685479297112831375473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47590247305729483775167297 35692685479297112831375473)
              ·
                refine ⟨26769514109472834623531605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35692685479297112831375473 26769514109472834623531605)
                ·
                  refine ⟨313705243470384780744511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26769514109472834623531605 313705243470384780744511)
                  ·
                    rfl

theorem cell23_5498449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_5498449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498449 prefixEnd_5498449 := by exact prefixLift 5498449
  have htrace : WordTrace (prefixWord ++ tailWord_5498449) baseStart_5498449 baseEnd_5498449 := by
    simpa [prefixWord, tailWord_5498449, baseEnd_5498449] using wordTrace_append hprefix tailTrace_5498449
  have hstable : (prefixWord ++ tailWord_5498449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498449).length < 2 ^ (prefixWord ++ tailWord_5498449).sum := by decide
  have hdescent : baseEnd_5498449 < baseStart_5498449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
