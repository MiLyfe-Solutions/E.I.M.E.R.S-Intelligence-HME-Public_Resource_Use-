import V185TrunkScan23Chunk1373

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8137673 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 7, 3, 2]
def baseStart_8137673 : Nat := 118140960795 + 8137673 * 2 ^ 59
def prefixEnd_8137673 : Nat := 4983230072969 + 3 ^ 40 * 8137673 * 2
def baseEnd_8137673 : Nat := 4178537658115245050663029

theorem tailTrace_8137673 : CollatzResearch.WordTrace tailWord_8137673 prefixEnd_8137673 4178537658115245050663029 := by
  unfold tailWord_8137673
  simp only [CollatzResearch.WordTrace]
  refine ⟨296805317847607999745569673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197870211898405333163713115 296805317847607999745569673)
  ·
    refine ⟨222603988385705999809177255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296805317847607999745569673 222603988385705999809177255)
    ·
      refine ⟨333905982578558999713765883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222603988385705999809177255 333905982578558999713765883)
      ·
        refine ⟨500858973867838499570648825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333905982578558999713765883 500858973867838499570648825)
        ·
          refine ⟨375644230400878874677986619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500858973867838499570648825 375644230400878874677986619)
          ·
            refine ⟨563466345601318312016979929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375644230400878874677986619 563466345601318312016979929)
            ·
              refine ⟨422599759200988734012734947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563466345601318312016979929 422599759200988734012734947)
              ·
                refine ⟨633899638801483101019102421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422599759200988734012734947 633899638801483101019102421)
                ·
                  refine ⟨14857022784409760180135213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 633899638801483101019102421 14857022784409760180135213)
                  ·
                    refine ⟨5571383544153660067550705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14857022784409760180135213 5571383544153660067550705)
                    ·
                      refine ⟨4178537658115245050663029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571383544153660067550705 4178537658115245050663029)
                      ·
                        rfl

theorem cell23_8137673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 3, 2].length) (baseStart_8137673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137673 prefixEnd_8137673 := by exact prefixLift 8137673
  have htrace : WordTrace (prefixWord ++ tailWord_8137673) baseStart_8137673 baseEnd_8137673 := by
    simpa [prefixWord, tailWord_8137673, baseEnd_8137673] using wordTrace_append hprefix tailTrace_8137673
  have hstable : (prefixWord ++ tailWord_8137673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137673).length < 2 ^ (prefixWord ++ tailWord_8137673).sum := by decide
  have hdescent : baseEnd_8137673 < baseStart_8137673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137690 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2]
def baseStart_8137690 : Nat := 118140960795 + 8137690 * 2 ^ 59
def prefixEnd_8137690 : Nat := 4983230072969 + 3 ^ 40 * 8137690 * 2
def baseEnd_8137690 : Nat := 4178546387286371484150451

theorem tailTrace_8137690 : CollatzResearch.WordTrace tailWord_8137690 prefixEnd_8137690 4178546387286371484150451 := by
  unfold tailWord_8137690
  simp only [CollatzResearch.WordTrace]
  refine ⟨74201484472136602912234631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197870625259030941099292349 74201484472136602912234631)
  ·
    refine ⟨111302226708204904368351947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74201484472136602912234631 111302226708204904368351947)
    ·
      refine ⟨166953340062307356552527921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111302226708204904368351947 166953340062307356552527921)
      ·
        refine ⟨125215005046730517414395941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166953340062307356552527921 125215005046730517414395941)
        ·
          refine ⟨23477813446261972015199239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125215005046730517414395941 23477813446261972015199239)
          ·
            refine ⟨35216720169392958022798859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23477813446261972015199239 35216720169392958022798859)
            ·
              refine ⟨52825080254089437034198289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35216720169392958022798859 52825080254089437034198289)
              ·
                refine ⟨39618810190567077775648717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52825080254089437034198289 39618810190567077775648717)
                ·
                  refine ⟨14857053821462654165868269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39618810190567077775648717 14857053821462654165868269)
                  ·
                    refine ⟨5571395183048495312200601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14857053821462654165868269 5571395183048495312200601)
                    ·
                      refine ⟨4178546387286371484150451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571395183048495312200601 4178546387286371484150451)
                      ·
                        rfl

theorem cell23_8137690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_8137690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137690 prefixEnd_8137690 := by exact prefixLift 8137690
  have htrace : WordTrace (prefixWord ++ tailWord_8137690) baseStart_8137690 baseEnd_8137690 := by
    simpa [prefixWord, tailWord_8137690, baseEnd_8137690] using wordTrace_append hprefix tailTrace_8137690
  have hstable : (prefixWord ++ tailWord_8137690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137690).length < 2 ^ (prefixWord ++ tailWord_8137690).sum := by decide
  have hdescent : baseEnd_8137690 < baseStart_8137690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137720 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 4, 2, 2]
def baseStart_8137720 : Nat := 118140960795 + 8137720 * 2 ^ 59
def prefixEnd_8137720 : Nat := 4983230072969 + 3 ^ 40 * 8137720 * 2
def baseEnd_8137720 : Nat := 4178561791706006366775313

theorem tailTrace_8137720 : CollatzResearch.WordTrace tailWord_8137720 prefixEnd_8137720 4178561791706006366775313 := by
  unfold tailWord_8137720
  simp only [CollatzResearch.WordTrace]
  refine ⟨148403516039218863386265307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197871354718958484515020409 148403516039218863386265307)
  ·
    refine ⟨222605274058828295079397961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148403516039218863386265307 222605274058828295079397961)
    ·
      refine ⟨166953955544121221309548471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222605274058828295079397961 166953955544121221309548471)
      ·
        refine ⟨250430933316181831964322707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166953955544121221309548471 250430933316181831964322707)
        ·
          refine ⟨375646399974272747946484061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250430933316181831964322707 375646399974272747946484061)
          ·
            refine ⟨140867399990352280479931523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375646399974272747946484061 140867399990352280479931523)
            ·
              refine ⟨211301099985528420719897285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140867399990352280479931523 211301099985528420719897285)
              ·
                refine ⟨39618956247286578884980741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211301099985528420719897285 39618956247286578884980741)
                ·
                  refine ⟨7428554296366233540933889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39618956247286578884980741 7428554296366233540933889)
                  ·
                    refine ⟨5571415722274675155700417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7428554296366233540933889 5571415722274675155700417)
                    ·
                      refine ⟨4178561791706006366775313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571415722274675155700417 4178561791706006366775313)
                      ·
                        rfl

theorem cell23_8137720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_8137720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137720 prefixEnd_8137720 := by exact prefixLift 8137720
  have htrace : WordTrace (prefixWord ++ tailWord_8137720) baseStart_8137720 baseEnd_8137720 := by
    simpa [prefixWord, tailWord_8137720, baseEnd_8137720] using wordTrace_append hprefix tailTrace_8137720
  have hstable : (prefixWord ++ tailWord_8137720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137720).length < 2 ^ (prefixWord ++ tailWord_8137720).sum := by decide
  have hdescent : baseEnd_8137720 < baseStart_8137720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137724 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_8137724 : Nat := 118140960795 + 8137724 * 2 ^ 59
def prefixEnd_8137724 : Nat := 4983230072969 + 3 ^ 40 * 8137724 * 2
def baseEnd_8137724 : Nat := 4178563845628624351125295

theorem tailTrace_8137724 : CollatzResearch.WordTrace tailWord_8137724 prefixEnd_8137724 4178563845628624351125295 := by
  unfold tailWord_8137724
  simp only [CollatzResearch.WordTrace]
  refine ⟨148403588985211617727838113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197871451980282156970450817 148403588985211617727838113)
  ·
    refine ⟨111302691738908713295878585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148403588985211617727838113 111302691738908713295878585)
    ·
      refine ⟨83477018804181534971908939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111302691738908713295878585 83477018804181534971908939)
      ·
        refine ⟨125215528206272302457863409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83477018804181534971908939 125215528206272302457863409)
        ·
          refine ⟨93911646154704226843397557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125215528206272302457863409 93911646154704226843397557)
          ·
            refine ⟨8804216827003521266568521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93911646154704226843397557 8804216827003521266568521)
            ·
              refine ⟨6603162620252640949926391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8804216827003521266568521 6603162620252640949926391)
              ·
                refine ⟨9904743930378961424889587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6603162620252640949926391 9904743930378961424889587)
                ·
                  refine ⟨14857115895568442137334381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9904743930378961424889587 14857115895568442137334381)
                  ·
                    refine ⟨5571418460838165801500393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14857115895568442137334381 5571418460838165801500393)
                    ·
                      refine ⟨4178563845628624351125295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571418460838165801500393 4178563845628624351125295)
                      ·
                        rfl

theorem cell23_8137724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_8137724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137724 prefixEnd_8137724 := by exact prefixLift 8137724
  have htrace : WordTrace (prefixWord ++ tailWord_8137724) baseStart_8137724 baseEnd_8137724 := by
    simpa [prefixWord, tailWord_8137724, baseEnd_8137724] using wordTrace_append hprefix tailTrace_8137724
  have hstable : (prefixWord ++ tailWord_8137724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137724).length < 2 ^ (prefixWord ++ tailWord_8137724).sum := by decide
  have hdescent : baseEnd_8137724 < baseStart_8137724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137753 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_8137753 : Nat := 118140960795 + 8137753 * 2 ^ 59
def prefixEnd_8137753 : Nat := 4983230072969 + 3 ^ 40 * 8137753 * 2
def baseEnd_8137753 : Nat := 4178578736567604737662661

theorem tailTrace_8137753 : CollatzResearch.WordTrace tailWord_8137753 prefixEnd_8137753 4178578736567604737662661 := by
  unfold tailWord_8137753
  simp only [CollatzResearch.WordTrace]
  refine ⟨296808235687318173408481913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197872157124878782272321275 296808235687318173408481913)
  ·
    refine ⟨222606176765488630056361435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296808235687318173408481913 222606176765488630056361435)
    ·
      refine ⟨333909265148232945084542153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222606176765488630056361435 333909265148232945084542153)
      ·
        refine ⟨250431948861174708813406615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333909265148232945084542153 250431948861174708813406615)
        ·
          refine ⟨375647923291762063220109923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250431948861174708813406615 375647923291762063220109923)
          ·
            refine ⟨563471884937643094830164885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375647923291762063220109923 563471884937643094830164885)
            ·
              refine ⟨26412744606452020070163979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 563471884937643094830164885 26412744606452020070163979)
              ·
                refine ⟨39619116909678030105245969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26412744606452020070163979 39619116909678030105245969)
                ·
                  refine ⟨29714337682258522578934477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39619116909678030105245969 29714337682258522578934477)
                  ·
                    refine ⟨11142876630846945967100429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29714337682258522578934477 11142876630846945967100429)
                    ·
                      refine ⟨4178578736567604737662661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11142876630846945967100429 4178578736567604737662661)
                      ·
                        rfl

theorem cell23_8137753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_8137753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137753 prefixEnd_8137753 := by exact prefixLift 8137753
  have htrace : WordTrace (prefixWord ++ tailWord_8137753) baseStart_8137753 baseEnd_8137753 := by
    simpa [prefixWord, tailWord_8137753, baseEnd_8137753] using wordTrace_append hprefix tailTrace_8137753
  have hstable : (prefixWord ++ tailWord_8137753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137753).length < 2 ^ (prefixWord ++ tailWord_8137753).sum := by decide
  have hdescent : baseEnd_8137753 < baseStart_8137753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137754 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2]
def baseStart_8137754 : Nat := 118140960795 + 8137754 * 2 ^ 59
def prefixEnd_8137754 : Nat := 4983230072969 + 3 ^ 40 * 8137754 * 2
def baseEnd_8137754 : Nat := 4178579250048259233750157

theorem tailTrace_8137754 : CollatzResearch.WordTrace tailWord_8137754 prefixEnd_8137754 4178579250048259233750157 := by
  unfold tailWord_8137754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74202068040078637644817079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197872181440209700386178877 74202068040078637644817079)
  ·
    refine ⟨111303102060117956467225619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74202068040078637644817079 111303102060117956467225619)
    ·
      refine ⟨166954653090176934700838429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111303102060117956467225619 166954653090176934700838429)
      ·
        refine ⟨62607994908816350512814411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166954653090176934700838429 62607994908816350512814411)
        ·
          refine ⟨93911992363224525769221617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62607994908816350512814411 93911992363224525769221617)
          ·
            refine ⟨70433994272418394326916213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93911992363224525769221617 70433994272418394326916213)
            ·
              refine ⟨6603186963039224468148395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70433994272418394326916213 6603186963039224468148395)
              ·
                refine ⟨9904780444558836702222593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6603186963039224468148395 9904780444558836702222593)
                ·
                  refine ⟨7428585333419127526666945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9904780444558836702222593 7428585333419127526666945)
                  ·
                    refine ⟨5571439000064345645000209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7428585333419127526666945 5571439000064345645000209)
                    ·
                      refine ⟨4178579250048259233750157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571439000064345645000209 4178579250048259233750157)
                      ·
                        rfl

theorem cell23_8137754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_8137754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137754 prefixEnd_8137754 := by exact prefixLift 8137754
  have htrace : WordTrace (prefixWord ++ tailWord_8137754) baseStart_8137754 baseEnd_8137754 := by
    simpa [prefixWord, tailWord_8137754, baseEnd_8137754] using wordTrace_append hprefix tailTrace_8137754
  have hstable : (prefixWord ++ tailWord_8137754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137754).length < 2 ^ (prefixWord ++ tailWord_8137754).sum := by decide
  have hdescent : baseEnd_8137754 < baseStart_8137754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137790 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_8137790 : Nat := 118140960795 + 8137790 * 2 ^ 59
def prefixEnd_8137790 : Nat := 4983230072969 + 3 ^ 40 * 8137790 * 2
def baseEnd_8137790 : Nat := 1392865911783940364299997

theorem tailTrace_8137790 : CollatzResearch.WordTrace tailWord_8137790 prefixEnd_8137790 1392865911783940364299997 := by
  unfold tailWord_8137790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37101198148523016090947353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197873056792122752485052549 37101198148523016090947353)
  ·
    refine ⟨27825898611392262068210515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37101198148523016090947353 27825898611392262068210515)
    ·
      refine ⟨41738847917088393102315773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27825898611392262068210515 41738847917088393102315773)
      ·
        refine ⟨15652067968908147413368415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41738847917088393102315773 15652067968908147413368415)
        ·
          refine ⟨23478101953362221120052623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15652067968908147413368415 23478101953362221120052623)
          ·
            refine ⟨35217152930043331680078935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23478101953362221120052623 35217152930043331680078935)
            ·
              refine ⟨52825729395064997520118403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35217152930043331680078935 52825729395064997520118403)
              ·
                refine ⟨79238594092597496280177605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52825729395064997520118403 79238594092597496280177605)
                ·
                  refine ⟨14857236392362030552533301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79238594092597496280177605 14857236392362030552533301)
                  ·
                    refine ⟨1392865911783940364299997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14857236392362030552533301 1392865911783940364299997)
                    ·
                      rfl

theorem cell23_8137790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_8137790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137790 prefixEnd_8137790 := by exact prefixLift 8137790
  have htrace : WordTrace (prefixWord ++ tailWord_8137790) baseStart_8137790 baseEnd_8137790 := by
    simpa [prefixWord, tailWord_8137790, baseEnd_8137790] using wordTrace_append hprefix tailTrace_8137790
  have hstable : (prefixWord ++ tailWord_8137790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137790).length < 2 ^ (prefixWord ++ tailWord_8137790).sum := by decide
  have hdescent : baseEnd_8137790 < baseStart_8137790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137820 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_8137820 : Nat := 118140960795 + 8137820 * 2 ^ 59
def prefixEnd_8137820 : Nat := 4983230072969 + 3 ^ 40 * 8137820 * 2
def baseEnd_8137820 : Nat := 1392871046590485325174951

theorem tailTrace_8137820 : CollatzResearch.WordTrace tailWord_8137820 prefixEnd_8137820 1392871046590485325174951 := by
  unfold tailWord_8137820
  simp only [CollatzResearch.WordTrace]
  refine ⟨148405339689037721925585457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197873786252050295900780609 148405339689037721925585457)
  ·
    refine ⟨111304004766778291444189093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148405339689037721925585457 111304004766778291444189093)
    ·
      refine ⟨20869500893770929645785455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111304004766778291444189093 20869500893770929645785455)
      ·
        refine ⟨31304251340656394468678183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20869500893770929645785455 31304251340656394468678183)
        ·
          refine ⟨46956377010984591703017275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31304251340656394468678183 46956377010984591703017275)
          ·
            refine ⟨70434565516476887554525913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46956377010984591703017275 70434565516476887554525913)
            ·
              refine ⟨52825924137357665665894435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70434565516476887554525913 52825924137357665665894435)
              ·
                refine ⟨79238886206036498498841653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52825924137357665665894435 79238886206036498498841653)
                ·
                  refine ⟨7428645581815921734266405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79238886206036498498841653 7428645581815921734266405)
                  ·
                    refine ⟨1392871046590485325174951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428645581815921734266405 1392871046590485325174951)
                    ·
                      rfl

theorem cell23_8137820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_8137820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137820 prefixEnd_8137820 := by exact prefixLift 8137820
  have htrace : WordTrace (prefixWord ++ tailWord_8137820) baseStart_8137820 baseEnd_8137820 := by
    simpa [prefixWord, tailWord_8137820, baseEnd_8137820] using wordTrace_append hprefix tailTrace_8137820
  have hstable : (prefixWord ++ tailWord_8137820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137820).length < 2 ^ (prefixWord ++ tailWord_8137820).sum := by decide
  have hdescent : baseEnd_8137820 < baseStart_8137820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137853 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_8137853 : Nat := 118140960795 + 8137853 * 2 ^ 59
def prefixEnd_8137853 : Nat := 4983230072969 + 3 ^ 40 * 8137853 * 2
def baseEnd_8137853 : Nat := 4178630084633054346412201

theorem tailTrace_8137853 : CollatzResearch.WordTrace tailWord_8137853 prefixEnd_8137853 4178630084633054346412201 := by
  unfold tailWord_8137853
  simp only [CollatzResearch.WordTrace]
  refine ⟨296811882986955890487122213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197874588657970593658081475 296811882986955890487122213)
  ·
    refine ⟨55652228060054229466335415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296811882986955890487122213 55652228060054229466335415)
    ·
      refine ⟨83478342090081344199503123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55652228060054229466335415 83478342090081344199503123)
      ·
        refine ⟨125217513135122016299254685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83478342090081344199503123 125217513135122016299254685)
        ·
          refine ⟨46956567425670756112220507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125217513135122016299254685 46956567425670756112220507)
          ·
            refine ⟨70434851138506134168330761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46956567425670756112220507 70434851138506134168330761)
            ·
              refine ⟨52826138353879600626248071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70434851138506134168330761 52826138353879600626248071)
              ·
                refine ⟨79239207530819400939372107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52826138353879600626248071 79239207530819400939372107)
                ·
                  refine ⟨118858811296229101409058161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79239207530819400939372107 118858811296229101409058161)
                  ·
                    refine ⟨89144108472171826056793621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118858811296229101409058161 89144108472171826056793621)
                    ·
                      refine ⟨4178630084633054346412201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89144108472171826056793621 4178630084633054346412201)
                      ·
                        rfl

theorem cell23_8137853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_8137853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137853 prefixEnd_8137853 := by exact prefixLift 8137853
  have htrace : WordTrace (prefixWord ++ tailWord_8137853) baseStart_8137853 baseEnd_8137853 := by
    simpa [prefixWord, tailWord_8137853, baseEnd_8137853] using wordTrace_append hprefix tailTrace_8137853
  have hstable : (prefixWord ++ tailWord_8137853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137853).length < 2 ^ (prefixWord ++ tailWord_8137853).sum := by decide
  have hdescent : baseEnd_8137853 < baseStart_8137853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137880 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_8137880 : Nat := 118140960795 + 8137880 * 2 ^ 59
def prefixEnd_8137880 : Nat := 4983230072969 + 3 ^ 40 * 8137880 * 2
def baseEnd_8137880 : Nat := 1392881316203575246924859

theorem tailTrace_8137880 : CollatzResearch.WordTrace tailWord_8137880 prefixEnd_8137880 1392881316203575246924859 := by
  unfold tailWord_8137880
  simp only [CollatzResearch.WordTrace]
  refine ⟨148406433878929037049177547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197875245171905382732236729 148406433878929037049177547)
  ·
    refine ⟨222609650818393555573766321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148406433878929037049177547 222609650818393555573766321)
    ·
      refine ⟨166957238113795166680324741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222609650818393555573766321 166957238113795166680324741)
      ·
        refine ⟨31304482146336593752560889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166957238113795166680324741 31304482146336593752560889)
        ·
          refine ⟨23478361609752445314420667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31304482146336593752560889 23478361609752445314420667)
          ·
            refine ⟨35217542414628667971631001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23478361609752445314420667 35217542414628667971631001)
            ·
              refine ⟨26413156810971500978723251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35217542414628667971631001 26413156810971500978723251)
              ·
                refine ⟨39619735216457251468084877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26413156810971500978723251 39619735216457251468084877)
                ·
                  refine ⟨14857400706171469300531829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39619735216457251468084877 14857400706171469300531829)
                  ·
                    refine ⟨1392881316203575246924859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14857400706171469300531829 1392881316203575246924859)
                    ·
                      rfl

theorem cell23_8137880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_8137880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137880 prefixEnd_8137880 := by exact prefixLift 8137880
  have htrace : WordTrace (prefixWord ++ tailWord_8137880) baseStart_8137880 baseEnd_8137880 := by
    simpa [prefixWord, tailWord_8137880, baseEnd_8137880] using wordTrace_append hprefix tailTrace_8137880
  have hstable : (prefixWord ++ tailWord_8137880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137880).length < 2 ^ (prefixWord ++ tailWord_8137880).sum := by decide
  have hdescent : baseEnd_8137880 < baseStart_8137880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137930 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_8137930 : Nat := 118140960795 + 8137930 * 2 ^ 59
def prefixEnd_8137930 : Nat := 4983230072969 + 3 ^ 40 * 8137930 * 2
def baseEnd_8137930 : Nat := 4178669622643450545149347

theorem tailTrace_8137930 : CollatzResearch.WordTrace tailWord_8137930 prefixEnd_8137930 4178669622643450545149347 := by
  unfold tailWord_8137930
  simp only [CollatzResearch.WordTrace]
  refine ⟨74203672851919233159418811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197876460938451288425116829 74203672851919233159418811)
  ·
    refine ⟨111305509277878849739128217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74203672851919233159418811 111305509277878849739128217)
    ·
      refine ⟨83479131958409137304346163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111305509277878849739128217 83479131958409137304346163)
      ·
        refine ⟨125218697937613705956519245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83479131958409137304346163 125218697937613705956519245)
        ·
          refine ⟨46957011726605139733694717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125218697937613705956519245 46957011726605139733694717)
          ·
            refine ⟨17608879397476927400135519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46957011726605139733694717 17608879397476927400135519)
            ·
              refine ⟨26413319096215391100203279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17608879397476927400135519 26413319096215391100203279)
              ·
                refine ⟨39619978644323086650304919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26413319096215391100203279 39619978644323086650304919)
                ·
                  refine ⟨59429967966484629975457379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39619978644323086650304919 59429967966484629975457379)
                  ·
                    refine ⟨89144951949726944963186069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59429967966484629975457379 89144951949726944963186069)
                    ·
                      refine ⟨4178669622643450545149347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89144951949726944963186069 4178669622643450545149347)
                      ·
                        rfl

theorem cell23_8137930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_8137930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137930 prefixEnd_8137930 := by exact prefixLift 8137930
  have htrace : WordTrace (prefixWord ++ tailWord_8137930) baseStart_8137930 baseEnd_8137930 := by
    simpa [prefixWord, tailWord_8137930, baseEnd_8137930] using wordTrace_append hprefix tailTrace_8137930
  have hstable : (prefixWord ++ tailWord_8137930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137930).length < 2 ^ (prefixWord ++ tailWord_8137930).sum := by decide
  have hdescent : baseEnd_8137930 < baseStart_8137930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137934 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_8137934 : Nat := 118140960795 + 8137934 * 2 ^ 59
def prefixEnd_8137934 : Nat := 4983230072969 + 3 ^ 40 * 8137934 * 2
def baseEnd_8137934 : Nat := 4178671676566068529499329

theorem tailTrace_8137934 : CollatzResearch.WordTrace tailWord_8137934 prefixEnd_8137934 4178671676566068529499329 := by
  unfold tailWord_8137934
  simp only [CollatzResearch.WordTrace]
  refine ⟨37101854662457805165102607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197876558199774960880547237 37101854662457805165102607)
  ·
    refine ⟨55652781993686707747653911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37101854662457805165102607 55652781993686707747653911)
    ·
      refine ⟨83479172990530061621480867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55652781993686707747653911 83479172990530061621480867)
      ·
        refine ⟨125218759485795092432221301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83479172990530061621480867 125218759485795092432221301)
        ·
          refine ⟨11739258701793289915520747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125218759485795092432221301 11739258701793289915520747)
          ·
            refine ⟨17608888052689934873281121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739258701793289915520747 17608888052689934873281121)
            ·
              refine ⟨13206666039517451154960841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17608888052689934873281121 13206666039517451154960841)
              ·
                refine ⟨9904999529638088366220631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13206666039517451154960841 9904999529638088366220631)
                ·
                  refine ⟨14857499294457132549330947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9904999529638088366220631 14857499294457132549330947)
                  ·
                    refine ⟨22286248941685698823996421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14857499294457132549330947 22286248941685698823996421)
                    ·
                      refine ⟨4178671676566068529499329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22286248941685698823996421 4178671676566068529499329)
                      ·
                        rfl

theorem cell23_8137934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_8137934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137934 prefixEnd_8137934 := by exact prefixLift 8137934
  have htrace : WordTrace (prefixWord ++ tailWord_8137934) baseStart_8137934 baseEnd_8137934 := by
    simpa [prefixWord, tailWord_8137934, baseEnd_8137934] using wordTrace_append hprefix tailTrace_8137934
  have hstable : (prefixWord ++ tailWord_8137934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137934).length < 2 ^ (prefixWord ++ tailWord_8137934).sum := by decide
  have hdescent : baseEnd_8137934 < baseStart_8137934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137951 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 1, 2, 2]
def baseStart_8137951 : Nat := 118140960795 + 8137951 * 2 ^ 59
def prefixEnd_8137951 : Nat := 4983230072969 + 3 ^ 40 * 8137951 * 2
def baseEnd_8137951 : Nat := 4178680405737194962986751

theorem tailTrace_8137951 : CollatzResearch.WordTrace tailWord_8137951 prefixEnd_8137951 4178680405737194962986751 := by
  unfold tailWord_8137951
  simp only [CollatzResearch.WordTrace]
  refine ⟨296815457340600853224189707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197876971560400568816126471 296815457340600853224189707)
  ·
    refine ⟨445223186010901279836284561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296815457340600853224189707 445223186010901279836284561)
    ·
      refine ⟨333917389508175959877213421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445223186010901279836284561 333917389508175959877213421)
      ·
        refine ⟨125219021065565984953955033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333917389508175959877213421 125219021065565984953955033)
        ·
          refine ⟨93914265799174488715466275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125219021065565984953955033 93914265799174488715466275)
          ·
            refine ⟨140871398698761733073199413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93914265799174488715466275 140871398698761733073199413)
            ·
              refine ⟨13206693628008912475612445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140871398698761733073199413 13206693628008912475612445)
              ·
                refine ⟨4952510110503342178354667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13206693628008912475612445 4952510110503342178354667)
                ·
                  refine ⟨7428765165755013267532001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952510110503342178354667 7428765165755013267532001)
                  ·
                    refine ⟨5571573874316259950649001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7428765165755013267532001 5571573874316259950649001)
                    ·
                      refine ⟨4178680405737194962986751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571573874316259950649001 4178680405737194962986751)
                      ·
                        rfl

theorem cell23_8137951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_8137951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137951 prefixEnd_8137951 := by exact prefixLift 8137951
  have htrace : WordTrace (prefixWord ++ tailWord_8137951) baseStart_8137951 baseEnd_8137951 := by
    simpa [prefixWord, tailWord_8137951, baseEnd_8137951] using wordTrace_append hprefix tailTrace_8137951
  have hstable : (prefixWord ++ tailWord_8137951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137951).length < 2 ^ (prefixWord ++ tailWord_8137951).sum := by decide
  have hdescent : baseEnd_8137951 < baseStart_8137951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137957 : List Nat := [1, 3, 1, 4, 4, 1, 9]
def baseStart_8137957 : Nat := 118140960795 + 8137957 * 2 ^ 59
def prefixEnd_8137957 : Nat := 4983230072969 + 3 ^ 40 * 8137957 * 2
def baseEnd_8137957 : Nat := 51588685020013851105083

theorem tailTrace_8137957 : CollatzResearch.WordTrace tailWord_8137957 prefixEnd_8137957 51588685020013851105083 := by
  unfold tailWord_8137957
  simp only [CollatzResearch.WordTrace]
  refine ⟨296815676178579116248908125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197877117452386077499272083 296815676178579116248908125)
  ·
    refine ⟨111305878566967168593340547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296815676178579116248908125 111305878566967168593340547)
    ·
      refine ⟨166958817850450752890010821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111305878566967168593340547 166958817850450752890010821)
      ·
        refine ⟨31304778346959516166877029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166958817850450752890010821 31304778346959516166877029)
        ·
          refine ⟨5869645940054909281289443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31304778346959516166877029 5869645940054909281289443)
          ·
            refine ⟨8804468910082363921934165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869645940054909281289443 8804468910082363921934165)
            ·
              refine ⟨51588685020013851105083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8804468910082363921934165 51588685020013851105083)
              ·
                rfl

theorem cell23_8137957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 9].length) (baseStart_8137957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137957 prefixEnd_8137957 := by exact prefixLift 8137957
  have htrace : WordTrace (prefixWord ++ tailWord_8137957) baseStart_8137957 baseEnd_8137957 := by
    simpa [prefixWord, tailWord_8137957, baseEnd_8137957] using wordTrace_append hprefix tailTrace_8137957
  have hstable : (prefixWord ++ tailWord_8137957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137957).length < 2 ^ (prefixWord ++ tailWord_8137957).sum := by decide
  have hdescent : baseEnd_8137957 < baseStart_8137957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8137977 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 3, 3, 2]
def baseStart_8137977 : Nat := 118140960795 + 8137977 * 2 ^ 59
def prefixEnd_8137977 : Nat := 4983230072969 + 3 ^ 40 * 8137977 * 2
def baseEnd_8137977 : Nat := 4178693756234211861261631

theorem tailTrace_8137977 : CollatzResearch.WordTrace tailWord_8137977 prefixEnd_8137977 4178693756234211861261631 := by
  unfold tailWord_8137977
  simp only [CollatzResearch.WordTrace]
  refine ⟨296816405638506659664636185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197877603759004439776424123 296816405638506659664636185)
  ·
    refine ⟨222612304228879994748477139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296816405638506659664636185 222612304228879994748477139)
    ·
      refine ⟨333918456343319992122715709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222612304228879994748477139 333918456343319992122715709)
      ·
        refine ⟨125219421128744997046018391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333918456343319992122715709 125219421128744997046018391)
        ·
          refine ⟨187829131693117495569027587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125219421128744997046018391 187829131693117495569027587)
          ·
            refine ⟨281743697539676243353541381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187829131693117495569027587 281743697539676243353541381)
            ·
              refine ⟨52826943288689295628789009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281743697539676243353541381 52826943288689295628789009)
              ·
                refine ⟨39620207466516971721591757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52826943288689295628789009 39620207466516971721591757)
                ·
                  refine ⟨14857577799943864395596909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39620207466516971721591757 14857577799943864395596909)
                  ·
                    refine ⟨5571591674978949148348841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14857577799943864395596909 5571591674978949148348841)
                    ·
                      refine ⟨4178693756234211861261631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571591674978949148348841 4178693756234211861261631)
                      ·
                        rfl

theorem cell23_8137977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_8137977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8137977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8137977 prefixEnd_8137977 := by exact prefixLift 8137977
  have htrace : WordTrace (prefixWord ++ tailWord_8137977) baseStart_8137977 baseEnd_8137977 := by
    simpa [prefixWord, tailWord_8137977, baseEnd_8137977] using wordTrace_append hprefix tailTrace_8137977
  have hstable : (prefixWord ++ tailWord_8137977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8137977).length < 2 ^ (prefixWord ++ tailWord_8137977).sum := by decide
  have hdescent : baseEnd_8137977 < baseStart_8137977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8137977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138037 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_8138037 : Nat := 118140960795 + 8138037 * 2 ^ 59
def prefixEnd_8138037 : Nat := 4983230072969 + 3 ^ 40 * 8138037 * 2
def baseEnd_8138037 : Nat := 4178724565073481626511355

theorem tailTrace_8138037 : CollatzResearch.WordTrace tailWord_8138037 prefixEnd_8138037 4178724565073481626511355 := by
  unfold tailWord_8138037
  simp only [CollatzResearch.WordTrace]
  refine ⟨296818594018289289911820365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197879062678859526607880243 296818594018289289911820365)
  ·
    refine ⟨111306972756858483716932637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296818594018289289911820365 111306972756858483716932637)
    ·
      refine ⟨41740114783821931393849739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111306972756858483716932637 41740114783821931393849739)
      ·
        refine ⟨62610172175732897090774609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41740114783821931393849739 62610172175732897090774609)
        ·
          refine ⟨46957629131799672818080957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62610172175732897090774609 46957629131799672818080957)
          ·
            refine ⟨17609110924424877306780359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46957629131799672818080957 17609110924424877306780359)
            ·
              refine ⟨26413666386637315960170539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17609110924424877306780359 26413666386637315960170539)
              ·
                refine ⟨39620499579955973940255809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26413666386637315960170539 39620499579955973940255809)
                ·
                  refine ⟨29715374684966980455191857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39620499579955973940255809 29715374684966980455191857)
                  ·
                    refine ⟨22286531013725235341393893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29715374684966980455191857 22286531013725235341393893)
                    ·
                      refine ⟨4178724565073481626511355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22286531013725235341393893 4178724565073481626511355)
                      ·
                        rfl

theorem cell23_8138037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_8138037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138037 prefixEnd_8138037 := by exact prefixLift 8138037
  have htrace : WordTrace (prefixWord ++ tailWord_8138037) baseStart_8138037 baseEnd_8138037 := by
    simpa [prefixWord, tailWord_8138037, baseEnd_8138037] using wordTrace_append hprefix tailTrace_8138037
  have hstable : (prefixWord ++ tailWord_8138037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138037).length < 2 ^ (prefixWord ++ tailWord_8138037).sum := by decide
  have hdescent : baseEnd_8138037 < baseStart_8138037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138041 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 1, 4, 2]
def baseStart_8138041 : Nat := 118140960795 + 8138041 * 2 ^ 59
def prefixEnd_8138041 : Nat := 4983230072969 + 3 ^ 40 * 8138041 * 2
def baseEnd_8138041 : Nat := 4178726618996099610861337

theorem tailTrace_8138041 : CollatzResearch.WordTrace tailWord_8138041 prefixEnd_8138041 4178726618996099610861337 := by
  unfold tailWord_8138041
  simp only [CollatzResearch.WordTrace]
  refine ⟨296818739910274798594965977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197879159940183199063310651 296818739910274798594965977)
  ·
    refine ⟨222614054932706098946224483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296818739910274798594965977 222614054932706098946224483)
    ·
      refine ⟨333921082399059148419336725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222614054932706098946224483 333921082399059148419336725)
      ·
        refine ⟨15652550737455897582156409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333921082399059148419336725 15652550737455897582156409)
        ·
          refine ⟨11739413053091923186617307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15652550737455897582156409 11739413053091923186617307)
          ·
            refine ⟨17609119579637884779925961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739413053091923186617307 17609119579637884779925961)
            ·
              refine ⟨13206839684728413584944471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17609119579637884779925961 13206839684728413584944471)
              ·
                refine ⟨19810259527092620377416707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13206839684728413584944471 19810259527092620377416707)
                ·
                  refine ⟨29715389290638930566125061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19810259527092620377416707 29715389290638930566125061)
                  ·
                    refine ⟨5571635491994799481148449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29715389290638930566125061 5571635491994799481148449)
                    ·
                      refine ⟨4178726618996099610861337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571635491994799481148449 4178726618996099610861337)
                      ·
                        rfl

theorem cell23_8138041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_8138041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138041 prefixEnd_8138041 := by exact prefixLift 8138041
  have htrace : WordTrace (prefixWord ++ tailWord_8138041) baseStart_8138041 baseEnd_8138041 := by
    simpa [prefixWord, tailWord_8138041, baseEnd_8138041] using wordTrace_append hprefix tailTrace_8138041
  have hstable : (prefixWord ++ tailWord_8138041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138041).length < 2 ^ (prefixWord ++ tailWord_8138041).sum := by decide
  have hdescent : baseEnd_8138041 < baseStart_8138041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138107 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 3, 4]
def baseStart_8138107 : Nat := 118140960795 + 8138107 * 2 ^ 59
def prefixEnd_8138107 : Nat := 4983230072969 + 3 ^ 40 * 8138107 * 2
def baseEnd_8138107 : Nat := 1392920169573098784212011

theorem tailTrace_8138107 : CollatzResearch.WordTrace tailWord_8138107 prefixEnd_8138107 1392920169573098784212011 := by
  unfold tailWord_8138107
  simp only [CollatzResearch.WordTrace]
  refine ⟨296821147128035691866868575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197880764752023794577912383 296821147128035691866868575)
  ·
    refine ⟨445231720692053537800302863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296821147128035691866868575 445231720692053537800302863)
    ·
      refine ⟨667847581038080306700454295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445231720692053537800302863 667847581038080306700454295)
      ·
        refine ⟨1001771371557120460050681443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667847581038080306700454295 1001771371557120460050681443)
        ·
          refine ⟨1502657057335680690076022165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001771371557120460050681443 1502657057335680690076022165)
          ·
            refine ⟨70437049562610032347313539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1502657057335680690076022165 70437049562610032347313539)
            ·
              refine ⟨105655574343915048520970309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70437049562610032347313539 105655574343915048520970309)
              ·
                refine ⟨19810420189484071597681933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105655574343915048520970309 19810420189484071597681933)
                ·
                  refine ⟨7428907571056526849130725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19810420189484071597681933 7428907571056526849130725)
                  ·
                    refine ⟨1392920169573098784212011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428907571056526849130725 1392920169573098784212011)
                    ·
                      rfl

theorem cell23_8138107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 4].length) (baseStart_8138107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138107 prefixEnd_8138107 := by exact prefixLift 8138107
  have htrace : WordTrace (prefixWord ++ tailWord_8138107) baseStart_8138107 baseEnd_8138107 := by
    simpa [prefixWord, tailWord_8138107, baseEnd_8138107] using wordTrace_append hprefix tailTrace_8138107
  have hstable : (prefixWord ++ tailWord_8138107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138107).length < 2 ^ (prefixWord ++ tailWord_8138107).sum := by decide
  have hdescent : baseEnd_8138107 < baseStart_8138107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138117 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_8138117 : Nat := 118140960795 + 8138117 * 2 ^ 59
def prefixEnd_8138117 : Nat := 4983230072969 + 3 ^ 40 * 8138117 * 2
def baseEnd_8138117 : Nat := 4178765643525841313510987

theorem tailTrace_8138117 : CollatzResearch.WordTrace tailWord_8138117 prefixEnd_8138117 4178765643525841313510987 := by
  unfold tailWord_8138117
  simp only [CollatzResearch.WordTrace]
  refine ⟨296821511857999463574732605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197881007905332975716488403 296821511857999463574732605)
  ·
    refine ⟨111308066946749798840524727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296821511857999463574732605 111308066946749798840524727)
    ·
      refine ⟨166962100420124698260787091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111308066946749798840524727 166962100420124698260787091)
      ·
        refine ⟨250443150630187047391180637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166962100420124698260787091 250443150630187047391180637)
        ·
          refine ⟨93916181486320142771692739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250443150630187047391180637 93916181486320142771692739)
          ·
            refine ⟨140874272229480214157539109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93916181486320142771692739 140874272229480214157539109)
            ·
              refine ⟨26413926043027540154538583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140874272229480214157539109 26413926043027540154538583)
              ·
                refine ⟨39620889064541310231807875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26413926043027540154538583 39620889064541310231807875)
                ·
                  refine ⟨59431333596811965347711813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39620889064541310231807875 59431333596811965347711813)
                  ·
                    refine ⟨11143375049402243502695965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59431333596811965347711813 11143375049402243502695965)
                    ·
                      refine ⟨4178765643525841313510987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11143375049402243502695965 4178765643525841313510987)
                      ·
                        rfl

theorem cell23_8138117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_8138117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138117 prefixEnd_8138117 := by exact prefixLift 8138117
  have htrace : WordTrace (prefixWord ++ tailWord_8138117) baseStart_8138117 baseEnd_8138117 := by
    simpa [prefixWord, tailWord_8138117, baseEnd_8138117] using wordTrace_append hprefix tailTrace_8138117
  have hstable : (prefixWord ++ tailWord_8138117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138117).length < 2 ^ (prefixWord ++ tailWord_8138117).sum := by decide
  have hdescent : baseEnd_8138117 < baseStart_8138117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138141 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_8138141 : Nat := 118140960795 + 8138141 * 2 ^ 59
def prefixEnd_8138141 : Nat := 4983230072969 + 3 ^ 40 * 8138141 * 2
def baseEnd_8138141 : Nat := 1392925989020516406536959

theorem tailTrace_8138141 : CollatzResearch.WordTrace tailWord_8138141 prefixEnd_8138141 1392925989020516406536959 := by
  unfold tailWord_8138141
  simp only [CollatzResearch.WordTrace]
  refine ⟨296822387209912515673606277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197881591473275010449070851 296822387209912515673606277)
  ·
    refine ⟨55654197601858596688801177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296822387209912515673606277 55654197601858596688801177)
    ·
      refine ⟨41740648201393947516600883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55654197601858596688801177 41740648201393947516600883)
      ·
        refine ⟨62610972302090921274901325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41740648201393947516600883 62610972302090921274901325)
        ·
          refine ⟨23479114613284095478087997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62610972302090921274901325 23479114613284095478087997)
          ·
            refine ⟨8804667979981535804282999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23479114613284095478087997 8804667979981535804282999)
            ·
              refine ⟨13207001969972303706424499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804667979981535804282999 13207001969972303706424499)
              ·
                refine ⟨19810502954958455559636749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207001969972303706424499 19810502954958455559636749)
                ·
                  refine ⟨7428938608109420834863781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19810502954958455559636749 7428938608109420834863781)
                  ·
                    refine ⟨1392925989020516406536959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428938608109420834863781 1392925989020516406536959)
                    ·
                      rfl

theorem cell23_8138141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_8138141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138141 prefixEnd_8138141 := by exact prefixLift 8138141
  have htrace : WordTrace (prefixWord ++ tailWord_8138141) baseStart_8138141 baseEnd_8138141 := by
    simpa [prefixWord, tailWord_8138141, baseEnd_8138141] using wordTrace_append hprefix tailTrace_8138141
  have hstable : (prefixWord ++ tailWord_8138141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138141).length < 2 ^ (prefixWord ++ tailWord_8138141).sum := by decide
  have hdescent : baseEnd_8138141 < baseStart_8138141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138160 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_8138160 : Nat := 118140960795 + 8138160 * 2 ^ 59
def prefixEnd_8138160 : Nat := 4983230072969 + 3 ^ 40 * 8138160 * 2
def baseEnd_8138160 : Nat := 4178787723193984645273289

theorem tailTrace_8138160 : CollatzResearch.WordTrace tailWord_8138160 prefixEnd_8138160 4178787723193984645273289 := by
  unfold tailWord_8138160
  simp only [CollatzResearch.WordTrace]
  refine ⟨148411540098421840959273967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197882053464562454612365289 148411540098421840959273967)
  ·
    refine ⟨222617310147632761438910951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148411540098421840959273967 222617310147632761438910951)
    ·
      refine ⟨333925965221449142158366427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222617310147632761438910951 333925965221449142158366427)
      ·
        refine ⟨500888947832173713237549641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333925965221449142158366427 500888947832173713237549641)
        ·
          refine ⟨375666710874130284928162231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500888947832173713237549641 375666710874130284928162231)
          ·
            refine ⟨563500066311195427392243347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375666710874130284928162231 563500066311195427392243347)
            ·
              refine ⟨845250099466793141088365021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563500066311195427392243347 845250099466793141088365021)
              ·
                refine ⟨316968787300047427908136883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845250099466793141088365021 316968787300047427908136883)
                ·
                  refine ⟨475453180950071141862205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316968787300047427908136883 475453180950071141862205325)
                  ·
                    refine ⟨178294942856276678198326997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475453180950071141862205325 178294942856276678198326997)
                    ·
                      refine ⟨4178787723193984645273289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178294942856276678198326997 4178787723193984645273289)
                      ·
                        rfl

theorem cell23_8138160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_8138160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138160 prefixEnd_8138160 := by exact prefixLift 8138160
  have htrace : WordTrace (prefixWord ++ tailWord_8138160) baseStart_8138160 baseEnd_8138160 := by
    simpa [prefixWord, tailWord_8138160, baseEnd_8138160] using wordTrace_append hprefix tailTrace_8138160
  have hstable : (prefixWord ++ tailWord_8138160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138160).length < 2 ^ (prefixWord ++ tailWord_8138160).sum := by decide
  have hdescent : baseEnd_8138160 < baseStart_8138160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138167 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 3, 5]
def baseStart_8138167 : Nat := 118140960795 + 8138167 * 2 ^ 59
def prefixEnd_8138167 : Nat := 4983230072969 + 3 ^ 40 * 8138167 * 2
def baseEnd_8138167 : Nat := 1392930439186188705961919

theorem tailTrace_8138167 : CollatzResearch.WordTrace tailWord_8138167 prefixEnd_8138167 1392930439186188705961919 := by
  unfold tailWord_8138167
  simp only [CollatzResearch.WordTrace]
  refine ⟨296823335507818322114052755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197882223671878881409368503 296823335507818322114052755)
  ·
    refine ⟨445235003261727483171079133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296823335507818322114052755 445235003261727483171079133)
    ·
      refine ⟨166963126223147806189154675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445235003261727483171079133 166963126223147806189154675)
      ·
        refine ⟨250444689334721709283732013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166963126223147806189154675 250444689334721709283732013)
        ·
          refine ⟨93916758500520640981399505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250444689334721709283732013 93916758500520640981399505)
          ·
            refine ⟨70437568875390480736049629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93916758500520640981399505 70437568875390480736049629)
            ·
              refine ⟨26414088328271430276018611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70437568875390480736049629 26414088328271430276018611)
              ·
                refine ⟨39621132492407145414027917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26414088328271430276018611 39621132492407145414027917)
                ·
                  refine ⟨14857924684652679530260469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39621132492407145414027917 14857924684652679530260469)
                  ·
                    refine ⟨1392930439186188705961919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14857924684652679530260469 1392930439186188705961919)
                    ·
                      rfl

theorem cell23_8138167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_8138167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138167 prefixEnd_8138167 := by exact prefixLift 8138167
  have htrace : WordTrace (prefixWord ++ tailWord_8138167) baseStart_8138167 baseEnd_8138167 := by
    simpa [prefixWord, tailWord_8138167, baseEnd_8138167] using wordTrace_append hprefix tailTrace_8138167
  have hstable : (prefixWord ++ tailWord_8138167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138167).length < 2 ^ (prefixWord ++ tailWord_8138167).sum := by decide
  have hdescent : baseEnd_8138167 < baseStart_8138167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138197 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_8138197 : Nat := 118140960795 + 8138197 * 2 ^ 59
def prefixEnd_8138197 : Nat := 4983230072969 + 3 ^ 40 * 8138197 * 2
def baseEnd_8138197 : Nat := 1392935573992733666836873

theorem tailTrace_8138197 : CollatzResearch.WordTrace tailWord_8138197 prefixEnd_8138197 1392935573992733666836873 := by
  unfold tailWord_8138197
  simp only [CollatzResearch.WordTrace]
  refine ⟨296824429697709637237644845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197882953131806424825096563 296824429697709637237644845)
  ·
    refine ⟨111309161136641113964116817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296824429697709637237644845 111309161136641113964116817)
    ·
      refine ⟨83481870852480835473087613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111309161136641113964116817 83481870852480835473087613)
      ·
        refine ⟨31305701569680313302407855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83481870852480835473087613 31305701569680313302407855)
        ·
          refine ⟨46958552354520469953611783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31305701569680313302407855 46958552354520469953611783)
          ·
            refine ⟨70437828531780704930417675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46958552354520469953611783 70437828531780704930417675)
            ·
              refine ⟨105656742797671057395626513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70437828531780704930417675 105656742797671057395626513)
              ·
                refine ⟨79242557098253293046719885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105656742797671057395626513 79242557098253293046719885)
                ·
                  refine ⟨29715958911844984892519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79242557098253293046719885 29715958911844984892519957)
                  ·
                    refine ⟨1392935573992733666836873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29715958911844984892519957 1392935573992733666836873)
                    ·
                      rfl

theorem cell23_8138197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_8138197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138197 prefixEnd_8138197 := by exact prefixLift 8138197
  have htrace : WordTrace (prefixWord ++ tailWord_8138197) baseStart_8138197 baseEnd_8138197 := by
    simpa [prefixWord, tailWord_8138197, baseEnd_8138197] using wordTrace_append hprefix tailTrace_8138197
  have hstable : (prefixWord ++ tailWord_8138197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138197).length < 2 ^ (prefixWord ++ tailWord_8138197).sum := by decide
  have hdescent : baseEnd_8138197 < baseStart_8138197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138207 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_8138207 : Nat := 118140960795 + 8138207 * 2 ^ 59
def prefixEnd_8138207 : Nat := 4983230072969 + 3 ^ 40 * 8138207 * 2
def baseEnd_8138207 : Nat := 4178811856784745961385573

theorem tailTrace_8138207 : CollatzResearch.WordTrace tailWord_8138207 prefixEnd_8138207 4178811856784745961385573 := by
  unfold tailWord_8138207
  simp only [CollatzResearch.WordTrace]
  refine ⟨296824794427673408945508875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197883196285115605963672583 296824794427673408945508875)
  ·
    refine ⟨445237191641510113418263313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296824794427673408945508875 445237191641510113418263313)
    ·
      refine ⟨333927893731132585063697485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445237191641510113418263313 333927893731132585063697485)
      ·
        refine ⟨125222960149174719398886557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333927893731132585063697485 125222960149174719398886557)
        ·
          refine ⟨46958610055940519774582459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125222960149174719398886557 46958610055940519774582459)
          ·
            refine ⟨70437915083910779661873689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46958610055940519774582459 70437915083910779661873689)
            ·
              refine ⟨52828436312933084746405267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70437915083910779661873689 52828436312933084746405267)
              ·
                refine ⟨79242654469399627119607901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52828436312933084746405267 79242654469399627119607901)
                ·
                  refine ⟨29715995426024860169852963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79242654469399627119607901 29715995426024860169852963)
                  ·
                    refine ⟨44573993139037290254779445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29715995426024860169852963 44573993139037290254779445)
                    ·
                      refine ⟨4178811856784745961385573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44573993139037290254779445 4178811856784745961385573)
                      ·
                        rfl

theorem cell23_8138207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_8138207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138207 prefixEnd_8138207 := by exact prefixLift 8138207
  have htrace : WordTrace (prefixWord ++ tailWord_8138207) baseStart_8138207 baseEnd_8138207 := by
    simpa [prefixWord, tailWord_8138207, baseEnd_8138207] using wordTrace_append hprefix tailTrace_8138207
  have hstable : (prefixWord ++ tailWord_8138207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138207).length < 2 ^ (prefixWord ++ tailWord_8138207).sum := by decide
  have hdescent : baseEnd_8138207 < baseStart_8138207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138224 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_8138224 : Nat := 118140960795 + 8138224 * 2 ^ 59
def prefixEnd_8138224 : Nat := 4983230072969 + 3 ^ 40 * 8138224 * 2
def baseEnd_8138224 : Nat := 4178820585955872394872995

theorem tailTrace_8138224 : CollatzResearch.WordTrace tailWord_8138224 prefixEnd_8138224 4178820585955872394872995 := by
  unfold tailWord_8138224
  simp only [CollatzResearch.WordTrace]
  refine ⟨148412707234305910424438863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197883609645741213899251817 148412707234305910424438863)
  ·
    refine ⟨222619060851458865636658295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148412707234305910424438863 222619060851458865636658295)
    ·
      refine ⟨333928591277188298454987443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222619060851458865636658295 333928591277188298454987443)
      ·
        refine ⟨500892886915782447682481165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333928591277188298454987443 500892886915782447682481165)
        ·
          refine ⟨187834832593418417880930437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500892886915782447682481165 187834832593418417880930437)
          ·
            refine ⟨35219031111265953352674457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187834832593418417880930437 35219031111265953352674457)
            ·
              refine ⟨26414273333449465014505843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35219031111265953352674457 26414273333449465014505843)
              ·
                refine ⟨39621410000174197521758765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26414273333449465014505843 39621410000174197521758765)
                ·
                  refine ⟨14858028750065324070659537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39621410000174197521758765 14858028750065324070659537)
                  ·
                    refine ⟨11143521562548993052994653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14858028750065324070659537 11143521562548993052994653)
                    ·
                      refine ⟨4178820585955872394872995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11143521562548993052994653 4178820585955872394872995)
                      ·
                        rfl

theorem cell23_8138224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_8138224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138224 prefixEnd_8138224 := by exact prefixLift 8138224
  have htrace : WordTrace (prefixWord ++ tailWord_8138224) baseStart_8138224 baseEnd_8138224 := by
    simpa [prefixWord, tailWord_8138224, baseEnd_8138224] using wordTrace_append hprefix tailTrace_8138224
  have hstable : (prefixWord ++ tailWord_8138224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138224).length < 2 ^ (prefixWord ++ tailWord_8138224).sum := by decide
  have hdescent : baseEnd_8138224 < baseStart_8138224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138244 : List Nat := [2, 3, 2, 3, 2, 1, 10]
def baseStart_8138244 : Nat := 118140960795 + 8138244 * 2 ^ 59
def prefixEnd_8138244 : Nat := 4983230072969 + 3 ^ 40 * 8138244 * 2
def baseEnd_8138244 : Nat := 51590504389740275513863

theorem tailTrace_8138244 : CollatzResearch.WordTrace tailWord_8138244 prefixEnd_8138244 51590504389740275513863 := by
  unfold tailWord_8138244
  simp only [CollatzResearch.WordTrace]
  refine ⟨148413071964269682132302893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197884095952359576176403857 148413071964269682132302893)
  ·
    refine ⟨55654901986601130799613585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148413071964269682132302893 55654901986601130799613585)
    ·
      refine ⟨41741176489950848099710189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55654901986601130799613585 41741176489950848099710189)
      ·
        refine ⟨15652941183731568037391321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41741176489950848099710189 15652941183731568037391321)
        ·
          refine ⟨11739705887798676028043491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15652941183731568037391321 11739705887798676028043491)
          ·
            refine ⟨17609558831698014042065237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739705887798676028043491 17609558831698014042065237)
            ·
              refine ⟨51590504389740275513863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17609558831698014042065237 51590504389740275513863)
              ·
                rfl

theorem cell23_8138244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 10].length) (baseStart_8138244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138244 prefixEnd_8138244 := by exact prefixLift 8138244
  have htrace : WordTrace (prefixWord ++ tailWord_8138244) baseStart_8138244 baseEnd_8138244 := by
    simpa [prefixWord, tailWord_8138244, baseEnd_8138244] using wordTrace_append hprefix tailTrace_8138244
  have hstable : (prefixWord ++ tailWord_8138244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138244).length < 2 ^ (prefixWord ++ tailWord_8138244).sum := by decide
  have hdescent : baseEnd_8138244 < baseStart_8138244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138271 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 3]
def baseStart_8138271 : Nat := 118140960795 + 8138271 * 2 ^ 59
def prefixEnd_8138271 : Nat := 4983230072969 + 3 ^ 40 * 8138271 * 2
def baseEnd_8138271 : Nat := 4178844719546633710985279

theorem tailTrace_8138271 : CollatzResearch.WordTrace tailWord_8138271 prefixEnd_8138271 4178844719546633710985279 := by
  unfold tailWord_8138271
  simp only [CollatzResearch.WordTrace]
  refine ⟨296827128699441547875838667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197884752466294365250559111 296827128699441547875838667)
  ·
    refine ⟨445240693049162321813758001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296827128699441547875838667 445240693049162321813758001)
    ·
      refine ⟨333930519786871741360318501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445240693049162321813758001 333930519786871741360318501)
      ·
        refine ⟨62611972460038451505059719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333930519786871741360318501 62611972460038451505059719)
        ·
          refine ⟨93917958690057677257589579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62611972460038451505059719 93917958690057677257589579)
          ·
            refine ⟨140876938035086515886384369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93917958690057677257589579 140876938035086515886384369)
            ·
              refine ⟨105657703526314886914788277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140876938035086515886384369 105657703526314886914788277)
              ·
                refine ⟨9905409705592020648261401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105657703526314886914788277 9905409705592020648261401)
                ·
                  refine ⟨7429057279194015486196051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9905409705592020648261401 7429057279194015486196051)
                  ·
                    refine ⟨11143585918791023229294077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429057279194015486196051 11143585918791023229294077)
                    ·
                      refine ⟨4178844719546633710985279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11143585918791023229294077 4178844719546633710985279)
                      ·
                        rfl

theorem cell23_8138271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_8138271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138271 prefixEnd_8138271 := by exact prefixLift 8138271
  have htrace : WordTrace (prefixWord ++ tailWord_8138271) baseStart_8138271 baseEnd_8138271 := by
    simpa [prefixWord, tailWord_8138271, baseEnd_8138271] using wordTrace_append hprefix tailTrace_8138271
  have hstable : (prefixWord ++ tailWord_8138271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138271).length < 2 ^ (prefixWord ++ tailWord_8138271).sum := by decide
  have hdescent : baseEnd_8138271 < baseStart_8138271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138314 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_8138314 : Nat := 118140960795 + 8138314 * 2 ^ 59
def prefixEnd_8138314 : Nat := 4983230072969 + 3 ^ 40 * 8138314 * 2
def baseEnd_8138314 : Nat := 4178866799214777042747581

theorem tailTrace_8138314 : CollatzResearch.WordTrace tailWord_8138314 prefixEnd_8138314 4178866799214777042747581 := by
  unfold tailWord_8138314
  simp only [CollatzResearch.WordTrace]
  refine ⟨74207174259571441554913499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197885798025523844146435997 74207174259571441554913499)
  ·
    refine ⟨111310761389357162332370249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74207174259571441554913499 111310761389357162332370249)
    ·
      refine ⟨83483071042017871749277687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111310761389357162332370249 83483071042017871749277687)
      ·
        refine ⟨125224606563026807623916531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83483071042017871749277687 125224606563026807623916531)
        ·
          refine ⟨187836909844540211435874797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125224606563026807623916531 187836909844540211435874797)
          ·
            refine ⟨70438841191702579288453049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187836909844540211435874797 70438841191702579288453049)
            ·
              refine ⟨52829130893776934466339787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70438841191702579288453049 52829130893776934466339787)
              ·
                refine ⟨79243696340665401699509681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52829130893776934466339787 79243696340665401699509681)
                ·
                  refine ⟨59432772255499051274632261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79243696340665401699509681 59432772255499051274632261)
                  ·
                    refine ⟨11143644797906072113993549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59432772255499051274632261 11143644797906072113993549)
                    ·
                      refine ⟨4178866799214777042747581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11143644797906072113993549 4178866799214777042747581)
                      ·
                        rfl

theorem cell23_8138314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_8138314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138314 prefixEnd_8138314 := by exact prefixLift 8138314
  have htrace : WordTrace (prefixWord ++ tailWord_8138314) baseStart_8138314 baseEnd_8138314 := by
    simpa [prefixWord, tailWord_8138314, baseEnd_8138314] using wordTrace_append hprefix tailTrace_8138314
  have hstable : (prefixWord ++ tailWord_8138314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138314).length < 2 ^ (prefixWord ++ tailWord_8138314).sum := by decide
  have hdescent : baseEnd_8138314 < baseStart_8138314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138324 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_8138324 : Nat := 118140960795 + 8138324 * 2 ^ 59
def prefixEnd_8138324 : Nat := 4983230072969 + 3 ^ 40 * 8138324 * 2
def baseEnd_8138324 : Nat := 4178871934021322003622535

theorem tailTrace_8138324 : CollatzResearch.WordTrace tailWord_8138324 prefixEnd_8138324 4178871934021322003622535 := by
  unfold tailWord_8138324
  simp only [CollatzResearch.WordTrace]
  refine ⟨148414530884124768963759013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197886041178833025285012017 148414530884124768963759013)
  ·
    refine ⟨27827724540773394180704815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148414530884124768963759013 27827724540773394180704815)
    ·
      refine ⟨41741586811160091271057223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27827724540773394180704815 41741586811160091271057223)
      ·
        refine ⟨62612380216740136906585835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41741586811160091271057223 62612380216740136906585835)
        ·
          refine ⟨93918570325110205359878753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62612380216740136906585835 93918570325110205359878753)
          ·
            refine ⟨70438927743832654019909065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93918570325110205359878753 70438927743832654019909065)
            ·
              refine ⟨52829195807874490514931799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70438927743832654019909065 52829195807874490514931799)
              ·
                refine ⟨79243793711811735772397699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52829195807874490514931799 79243793711811735772397699)
                ·
                  refine ⟨118865690567717603658596549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79243793711811735772397699 118865690567717603658596549)
                  ·
                    refine ⟨22287316981447050685986853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118865690567717603658596549 22287316981447050685986853)
                    ·
                      refine ⟨4178871934021322003622535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22287316981447050685986853 4178871934021322003622535)
                      ·
                        rfl

theorem cell23_8138324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_8138324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138324 prefixEnd_8138324 := by exact prefixLift 8138324
  have htrace : WordTrace (prefixWord ++ tailWord_8138324) baseStart_8138324 baseEnd_8138324 := by
    simpa [prefixWord, tailWord_8138324, baseEnd_8138324] using wordTrace_append hprefix tailTrace_8138324
  have hstable : (prefixWord ++ tailWord_8138324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138324).length < 2 ^ (prefixWord ++ tailWord_8138324).sum := by decide
  have hdescent : baseEnd_8138324 < baseStart_8138324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138347 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 5, 7]
def baseStart_8138347 : Nat := 118140960795 + 8138347 * 2 ^ 59
def prefixEnd_8138347 : Nat := 4983230072969 + 3 ^ 40 * 8138347 * 2
def baseEnd_8138347 : Nat := 1392961248025458471211643

theorem tailTrace_8138347 : CollatzResearch.WordTrace tailWord_8138347 prefixEnd_8138347 1392961248025458471211643 := by
  unfold tailWord_8138347
  simp only [CollatzResearch.WordTrace]
  refine ⟨296829900647166212855605295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197886600431444141903736863 296829900647166212855605295)
  ·
    refine ⟨445244850970749319283407943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296829900647166212855605295 445244850970749319283407943)
    ·
      refine ⟨667867276456123978925111915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445244850970749319283407943 667867276456123978925111915)
      ·
        refine ⟨1001800914684185968387667873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667867276456123978925111915 1001800914684185968387667873)
        ·
          refine ⟨751350686013139476290750905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001800914684185968387667873 751350686013139476290750905)
          ·
            refine ⟨563513014509854607218063179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751350686013139476290750905 563513014509854607218063179)
            ·
              refine ⟨845269521764781910827094769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563513014509854607218063179 845269521764781910827094769)
              ·
                refine ⟨633952141323586433120321077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845269521764781910827094769 633952141323586433120321077)
                ·
                  refine ⟨59433013249086228105030101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 633952141323586433120321077 59433013249086228105030101)
                  ·
                    refine ⟨1392961248025458471211643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59433013249086228105030101 1392961248025458471211643)
                    ·
                      rfl

theorem cell23_8138347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_8138347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138347 prefixEnd_8138347 := by exact prefixLift 8138347
  have htrace : WordTrace (prefixWord ++ tailWord_8138347) baseStart_8138347 baseEnd_8138347 := by
    simpa [prefixWord, tailWord_8138347, baseEnd_8138347] using wordTrace_append hprefix tailTrace_8138347
  have hstable : (prefixWord ++ tailWord_8138347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138347).length < 2 ^ (prefixWord ++ tailWord_8138347).sum := by decide
  have hdescent : baseEnd_8138347 < baseStart_8138347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138384 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_8138384 : Nat := 118140960795 + 8138384 * 2 ^ 59
def prefixEnd_8138384 : Nat := 4983230072969 + 3 ^ 40 * 8138384 * 2
def baseEnd_8138384 : Nat := 4178902742860591768872259

theorem tailTrace_8138384 : CollatzResearch.WordTrace tailWord_8138384 prefixEnd_8138384 4178902742860591768872259 := by
  unfold tailWord_8138384
  simp only [CollatzResearch.WordTrace]
  refine ⟨148415625074016084087351103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197887500098688112116468137 148415625074016084087351103)
  ·
    refine ⟨222623437611024126131026655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148415625074016084087351103 222623437611024126131026655)
    ·
      refine ⟨333935156416536189196539983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222623437611024126131026655 333935156416536189196539983)
      ·
        refine ⟨500902734624804283794809975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333935156416536189196539983 500902734624804283794809975)
        ·
          refine ⟨751354101937206425692214963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500902734624804283794809975 751354101937206425692214963)
          ·
            refine ⟨1127031152905809638538322445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751354101937206425692214963 1127031152905809638538322445)
            ·
              refine ⟨422636682339678614451870917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1127031152905809638538322445 422636682339678614451870917)
              ·
                refine ⟨79244377938689740209725797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422636682339678614451870917 79244377938689740209725797)
                ·
                  refine ⟨14858320863504326289323587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79244377938689740209725797 14858320863504326289323587)
                  ·
                    refine ⟨22287481295256489433985381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14858320863504326289323587 22287481295256489433985381)
                    ·
                      refine ⟨4178902742860591768872259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22287481295256489433985381 4178902742860591768872259)
                      ·
                        rfl

theorem cell23_8138384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_8138384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138384 prefixEnd_8138384 := by exact prefixLift 8138384
  have htrace : WordTrace (prefixWord ++ tailWord_8138384) baseStart_8138384 baseEnd_8138384 := by
    simpa [prefixWord, tailWord_8138384, baseEnd_8138384] using wordTrace_append hprefix tailTrace_8138384
  have hstable : (prefixWord ++ tailWord_8138384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138384).length < 2 ^ (prefixWord ++ tailWord_8138384).sum := by decide
  have hdescent : baseEnd_8138384 < baseStart_8138384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138398 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_8138398 : Nat := 118140960795 + 8138398 * 2 ^ 59
def prefixEnd_8138398 : Nat := 4983230072969 + 3 ^ 40 * 8138398 * 2
def baseEnd_8138398 : Nat := 1392969977196584904699065

theorem tailTrace_8138398 : CollatzResearch.WordTrace tailWord_8138398 prefixEnd_8138398 1392969977196584904699065 := by
  unfold tailWord_8138398
  simp only [CollatzResearch.WordTrace]
  refine ⟨37103970096247681070713981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197887840513320965710474565 37103970096247681070713981)
  ·
    refine ⟨13913988786092880401517743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37103970096247681070713981 13913988786092880401517743)
    ·
      refine ⟨20870983179139320602276615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13913988786092880401517743 20870983179139320602276615)
      ·
        refine ⟨31306474768708980903414923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20870983179139320602276615 31306474768708980903414923)
        ·
          refine ⟨46959712153063471355122385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31306474768708980903414923 46959712153063471355122385)
          ·
            refine ⟨35219784114797603516341789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46959712153063471355122385 35219784114797603516341789)
            ·
              refine ⟨13207419043049101318628171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35219784114797603516341789 13207419043049101318628171)
              ·
                refine ⟨19811128564573651977942257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207419043049101318628171 19811128564573651977942257)
                ·
                  refine ⟨14858346423430238983456693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19811128564573651977942257 14858346423430238983456693)
                  ·
                    refine ⟨1392969977196584904699065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14858346423430238983456693 1392969977196584904699065)
                    ·
                      rfl

theorem cell23_8138398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_8138398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138398 prefixEnd_8138398 := by exact prefixLift 8138398
  have htrace : WordTrace (prefixWord ++ tailWord_8138398) baseStart_8138398 baseEnd_8138398 := by
    simpa [prefixWord, tailWord_8138398, baseEnd_8138398] using wordTrace_append hprefix tailTrace_8138398
  have hstable : (prefixWord ++ tailWord_8138398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138398).length < 2 ^ (prefixWord ++ tailWord_8138398).sum := by decide
  have hdescent : baseEnd_8138398 < baseStart_8138398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138401 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_8138401 : Nat := 118140960795 + 8138401 * 2 ^ 59
def prefixEnd_8138401 : Nat := 4983230072969 + 3 ^ 40 * 8138401 * 2
def baseEnd_8138401 : Nat := 4178911472031718202359681

theorem tailTrace_8138401 : CollatzResearch.WordTrace tailWord_8138401 prefixEnd_8138401 4178911472031718202359681 := by
  unfold tailWord_8138401
  simp only [CollatzResearch.WordTrace]
  refine ⟨296831870188970580078071057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197887913459313720052047371 296831870188970580078071057)
  ·
    refine ⟨222623902641727935058553293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296831870188970580078071057 222623902641727935058553293)
    ·
      refine ⟨83483963490647975646957485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222623902641727935058553293 83483963490647975646957485)
      ·
        refine ⟨31306486308992990867609057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83483963490647975646957485 31306486308992990867609057)
        ·
          refine ⟨23479864731744743150706793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31306486308992990867609057 23479864731744743150706793)
          ·
            refine ⟨17609898548808557363030095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23479864731744743150706793 17609898548808557363030095)
            ·
              refine ⟨26414847823212836044545143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17609898548808557363030095 26414847823212836044545143)
              ·
                refine ⟨39622271734819254066817715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26414847823212836044545143 39622271734819254066817715)
                ·
                  refine ⟨59433407602228881100226573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39622271734819254066817715 59433407602228881100226573)
                  ·
                    refine ⟨22287527850835830412584965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59433407602228881100226573 22287527850835830412584965)
                    ·
                      refine ⟨4178911472031718202359681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22287527850835830412584965 4178911472031718202359681)
                      ·
                        rfl

theorem cell23_8138401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_8138401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138401 prefixEnd_8138401 := by exact prefixLift 8138401
  have htrace : WordTrace (prefixWord ++ tailWord_8138401) baseStart_8138401 baseEnd_8138401 := by
    simpa [prefixWord, tailWord_8138401, baseEnd_8138401] using wordTrace_append hprefix tailTrace_8138401
  have hstable : (prefixWord ++ tailWord_8138401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138401).length < 2 ^ (prefixWord ++ tailWord_8138401).sum := by decide
  have hdescent : baseEnd_8138401 < baseStart_8138401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138428 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_8138428 : Nat := 118140960795 + 8138428 * 2 ^ 59
def prefixEnd_8138428 : Nat := 4983230072969 + 3 ^ 40 * 8138428 * 2
def baseEnd_8138428 : Nat := 1392975112003129865574019

theorem tailTrace_8138428 : CollatzResearch.WordTrace tailWord_8138428 prefixEnd_8138428 1392975112003129865574019 := by
  unfold tailWord_8138428
  simp only [CollatzResearch.WordTrace]
  refine ⟨148416427479936381844651969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197888569973248509126202625 148416427479936381844651969)
  ·
    refine ⟨111312320609952286383488977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148416427479936381844651969 111312320609952286383488977)
    ·
      refine ⟨83484240457464214787616733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111312320609952286383488977 83484240457464214787616733)
      ·
        refine ⟨31306590171549080545356275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83484240457464214787616733 31306590171549080545356275)
        ·
          refine ⟨46959885257323620818034413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31306590171549080545356275 46959885257323620818034413)
          ·
            refine ⟨17609956971496357806762905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46959885257323620818034413 17609956971496357806762905)
            ·
              refine ⟨13207467728622268355072179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17609956971496357806762905 13207467728622268355072179)
              ·
                refine ⟨19811201592933402532608269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207467728622268355072179 19811201592933402532608269)
                ·
                  refine ⟨7429200597350025949728101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19811201592933402532608269 7429200597350025949728101)
                  ·
                    refine ⟨1392975112003129865574019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429200597350025949728101 1392975112003129865574019)
                    ·
                      rfl

theorem cell23_8138428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_8138428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138428 prefixEnd_8138428 := by exact prefixLift 8138428
  have htrace : WordTrace (prefixWord ++ tailWord_8138428) baseStart_8138428 baseEnd_8138428 := by
    simpa [prefixWord, tailWord_8138428, baseEnd_8138428] using wordTrace_append hprefix tailTrace_8138428
  have hstable : (prefixWord ++ tailWord_8138428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138428).length < 2 ^ (prefixWord ++ tailWord_8138428).sum := by decide
  have hdescent : baseEnd_8138428 < baseStart_8138428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138445 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_8138445 : Nat := 118140960795 + 8138445 * 2 ^ 59
def prefixEnd_8138445 : Nat := 4983230072969 + 3 ^ 40 * 8138445 * 2
def baseEnd_8138445 : Nat := 1392978021726838676736493

theorem tailTrace_8138445 : CollatzResearch.WordTrace tailWord_8138445 prefixEnd_8138445 1392978021726838676736493 := by
  unfold tailWord_8138445
  simp only [CollatzResearch.WordTrace]
  refine ⟨296833475000811175592672789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197888983333874117061781859 296833475000811175592672789)
  ·
    refine ⟨13914069140663023855906537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296833475000811175592672789 13914069140663023855906537)
    ·
      refine ⟨10435551855497267891929903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13914069140663023855906537 10435551855497267891929903)
      ·
        refine ⟨15653327783245901837894855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10435551855497267891929903 15653327783245901837894855)
        ·
          refine ⟨23479991674868852756842283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15653327783245901837894855 23479991674868852756842283)
          ·
            refine ⟨35219987512303279135263425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23479991674868852756842283 35219987512303279135263425)
            ·
              refine ⟨26414990634227459351447569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35219987512303279135263425 26414990634227459351447569)
              ·
                refine ⟨19811242975670594513585677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26414990634227459351447569 19811242975670594513585677)
                ·
                  refine ⟨7429216115876472942594629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19811242975670594513585677 7429216115876472942594629)
                  ·
                    refine ⟨1392978021726838676736493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429216115876472942594629 1392978021726838676736493)
                    ·
                      rfl

theorem cell23_8138445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_8138445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138445 prefixEnd_8138445 := by exact prefixLift 8138445
  have htrace : WordTrace (prefixWord ++ tailWord_8138445) baseStart_8138445 baseEnd_8138445 := by
    simpa [prefixWord, tailWord_8138445, baseEnd_8138445] using wordTrace_append hprefix tailTrace_8138445
  have hstable : (prefixWord ++ tailWord_8138445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138445).length < 2 ^ (prefixWord ++ tailWord_8138445).sum := by decide
  have hdescent : baseEnd_8138445 < baseStart_8138445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138451 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 3]
def baseStart_8138451 : Nat := 118140960795 + 8138451 * 2 ^ 59
def prefixEnd_8138451 : Nat := 4983230072969 + 3 ^ 40 * 8138451 * 2
def baseEnd_8138451 : Nat := 4178937146064443006734451

theorem tailTrace_8138451 : CollatzResearch.WordTrace tailWord_8138451 prefixEnd_8138451 4178937146064443006734451 := by
  unfold tailWord_8138451
  simp only [CollatzResearch.WordTrace]
  refine ⟨296833693838789438617391207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197889129225859625744927471 296833693838789438617391207)
  ·
    refine ⟨445250540758184157926086811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296833693838789438617391207 445250540758184157926086811)
    ·
      refine ⟨667875811137276236889130217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445250540758184157926086811 667875811137276236889130217)
      ·
        refine ⟨500906858352957177666847663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667875811137276236889130217 500906858352957177666847663)
        ·
          refine ⟨751360287529435766500271495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500906858352957177666847663 751360287529435766500271495)
          ·
            refine ⟨1127040431294153649750407243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751360287529435766500271495 1127040431294153649750407243)
            ·
              refine ⟨1690560646941230474625610865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127040431294153649750407243 1690560646941230474625610865)
              ·
                refine ⟨1267920485205922855969208149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690560646941230474625610865 1267920485205922855969208149)
                ·
                  refine ⟨7429221593003454234194579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1267920485205922855969208149 7429221593003454234194579)
                  ·
                    refine ⟨11143832389505181351291869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429221593003454234194579 11143832389505181351291869)
                    ·
                      refine ⟨4178937146064443006734451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11143832389505181351291869 4178937146064443006734451)
                      ·
                        rfl

theorem cell23_8138451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_8138451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138451 prefixEnd_8138451 := by exact prefixLift 8138451
  have htrace : WordTrace (prefixWord ++ tailWord_8138451) baseStart_8138451 baseEnd_8138451 := by
    simpa [prefixWord, tailWord_8138451, baseEnd_8138451] using wordTrace_append hprefix tailTrace_8138451
  have hstable : (prefixWord ++ tailWord_8138451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138451).length < 2 ^ (prefixWord ++ tailWord_8138451).sum := by decide
  have hdescent : baseEnd_8138451 < baseStart_8138451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138491 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 6, 2]
def baseStart_8138491 : Nat := 118140960795 + 8138491 * 2 ^ 59
def prefixEnd_8138491 : Nat := 4983230072969 + 3 ^ 40 * 8138491 * 2
def baseEnd_8138491 : Nat := 4178957685290622850234267

theorem tailTrace_8138491 : CollatzResearch.WordTrace tailWord_8138491 prefixEnd_8138491 4178957685290622850234267 := by
  unfold tailWord_8138491
  simp only [CollatzResearch.WordTrace]
  refine ⟨296835152758644525448847327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197890101839096350299231551 296835152758644525448847327)
  ·
    refine ⟨445252729137966788173270991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296835152758644525448847327 445252729137966788173270991)
    ·
      refine ⟨667879093706950182259906487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445252729137966788173270991 667879093706950182259906487)
      ·
        refine ⟨1001818640560425273389859731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667879093706950182259906487 1001818640560425273389859731)
        ·
          refine ⟨1502727960840637910084789597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001818640560425273389859731 1502727960840637910084789597)
          ·
            refine ⟨563522985315239216281796099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1502727960840637910084789597 563522985315239216281796099)
            ·
              refine ⟨845284477972858824422694149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563522985315239216281796099 845284477972858824422694149)
              ·
                refine ⟨158490839619911029579255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845284477972858824422694149 158490839619911029579255153)
                ·
                  refine ⟨118868129714933272184441365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158490839619911029579255153 118868129714933272184441365)
                  ·
                    refine ⟨5571943580387497133645689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118868129714933272184441365 5571943580387497133645689)
                    ·
                      refine ⟨4178957685290622850234267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5571943580387497133645689 4178957685290622850234267)
                      ·
                        rfl

theorem cell23_8138491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6, 2].length) (baseStart_8138491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138491 prefixEnd_8138491 := by exact prefixLift 8138491
  have htrace : WordTrace (prefixWord ++ tailWord_8138491) baseStart_8138491 baseEnd_8138491 := by
    simpa [prefixWord, tailWord_8138491, baseEnd_8138491] using wordTrace_append hprefix tailTrace_8138491
  have hstable : (prefixWord ++ tailWord_8138491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138491).length < 2 ^ (prefixWord ++ tailWord_8138491).sum := by decide
  have hdescent : baseEnd_8138491 < baseStart_8138491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138508 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_8138508 : Nat := 118140960795 + 8138508 * 2 ^ 59
def prefixEnd_8138508 : Nat := 4983230072969 + 3 ^ 40 * 8138508 * 2
def baseEnd_8138508 : Nat := 4178966414461749283721689

theorem tailTrace_8138508 : CollatzResearch.WordTrace tailWord_8138508 prefixEnd_8138508 4178966414461749283721689 := by
  unfold tailWord_8138508
  simp only [CollatzResearch.WordTrace]
  refine ⟨148417886399791468676108089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197890515199721958234810785 148417886399791468676108089)
  ·
    refine ⟨111313414799843601507081067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148417886399791468676108089 111313414799843601507081067)
    ·
      refine ⟨166970122199765402260621601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111313414799843601507081067 166970122199765402260621601)
      ·
        refine ⟨125227591649824051695466201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166970122199765402260621601 125227591649824051695466201)
        ·
          refine ⟨93920693737368038771599651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125227591649824051695466201 93920693737368038771599651)
          ·
            refine ⟨140881040606052058157399477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93920693737368038771599651 140881040606052058157399477)
            ·
              refine ⟨13207597556817380452256201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140881040606052058157399477 13207597556817380452256201)
              ·
                refine ⟨9905698167613035339192151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13207597556817380452256201 9905698167613035339192151)
                ·
                  refine ⟨14858547251419553008788227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905698167613035339192151 14858547251419553008788227)
                  ·
                    refine ⟨22287820877129329513182341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14858547251419553008788227 22287820877129329513182341)
                    ·
                      refine ⟨4178966414461749283721689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22287820877129329513182341 4178966414461749283721689)
                      ·
                        rfl

theorem cell23_8138508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_8138508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138508 prefixEnd_8138508 := by exact prefixLift 8138508
  have htrace : WordTrace (prefixWord ++ tailWord_8138508) baseStart_8138508 baseEnd_8138508 := by
    simpa [prefixWord, tailWord_8138508, baseEnd_8138508] using wordTrace_append hprefix tailTrace_8138508
  have hstable : (prefixWord ++ tailWord_8138508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138508).length < 2 ^ (prefixWord ++ tailWord_8138508).sum := by decide
  have hdescent : baseEnd_8138508 < baseStart_8138508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138548 : List Nat := [2, 5, 1, 1, 2, 1, 3, 8]
def baseStart_8138548 : Nat := 118140960795 + 8138548 * 2 ^ 59
def prefixEnd_8138548 : Nat := 4983230072969 + 3 ^ 40 * 8138548 * 2
def baseEnd_8138548 : Nat := 154777294581034412119315

theorem tailTrace_8138548 : CollatzResearch.WordTrace tailWord_8138548 prefixEnd_8138548 154777294581034412119315 := by
  unfold tailWord_8138548
  simp only [CollatzResearch.WordTrace]
  refine ⟨148418615859719012091836149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197891487812958682789114865 148418615859719012091836149)
  ·
    refine ⟨13914245236848657383609639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148418615859719012091836149 13914245236848657383609639)
    ·
      refine ⟨20871367855272986075414459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13914245236848657383609639 20871367855272986075414459)
      ·
        refine ⟨31307051782909479113121689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20871367855272986075414459 31307051782909479113121689)
        ·
          refine ⟨23480288837182109334841267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31307051782909479113121689 23480288837182109334841267)
          ·
            refine ⟨35220433255773164002261901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23480288837182109334841267 35220433255773164002261901)
            ·
              refine ⟨13207662470914936500848213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35220433255773164002261901 13207662470914936500848213)
              ·
                refine ⟨154777294581034412119315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13207662470914936500848213 154777294581034412119315)
                ·
                  rfl

theorem cell23_8138548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 8].length) (baseStart_8138548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138548 prefixEnd_8138548 := by exact prefixLift 8138548
  have htrace : WordTrace (prefixWord ++ tailWord_8138548) baseStart_8138548 baseEnd_8138548 := by
    simpa [prefixWord, tailWord_8138548, baseEnd_8138548] using wordTrace_append hprefix tailTrace_8138548
  have hstable : (prefixWord ++ tailWord_8138548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138548).length < 2 ^ (prefixWord ++ tailWord_8138548).sum := by decide
  have hdescent : baseEnd_8138548 < baseStart_8138548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138585 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 1, 3, 2]
def baseStart_8138585 : Nat := 118140960795 + 8138585 * 2 ^ 59
def prefixEnd_8138585 : Nat := 4983230072969 + 3 ^ 40 * 8138585 * 2
def baseEnd_8138585 : Nat := 4179005952472145482458835

theorem tailTrace_8138585 : CollatzResearch.WordTrace tailWord_8138585 prefixEnd_8138585 4179005952472145482458835 := by
  unfold tailWord_8138585
  simp only [CollatzResearch.WordTrace]
  refine ⟨296838581220303979502769209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197892387480202653001846139 296838581220303979502769209)
  ·
    refine ⟨222628935915227984627076907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296838581220303979502769209 222628935915227984627076907)
    ·
      refine ⟨333943403872841976940615361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222628935915227984627076907 333943403872841976940615361)
      ·
        refine ⟨250457552904631482705461521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333943403872841976940615361 250457552904631482705461521)
        ·
          refine ⟨187843164678473612029096141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250457552904631482705461521 187843164678473612029096141)
          ·
            refine ⟨70441186754427604510911053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187843164678473612029096141 70441186754427604510911053)
            ·
              refine ⟨26415445032910351691591645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70441186754427604510911053 26415445032910351691591645)
              ·
                refine ⟨9905791887341381884346867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26415445032910351691591645 9905791887341381884346867)
                ·
                  refine ⟨14858687831012072826520301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905791887341381884346867 14858687831012072826520301)
                  ·
                    refine ⟨5572007936629527309945113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14858687831012072826520301 5572007936629527309945113)
                    ·
                      refine ⟨4179005952472145482458835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572007936629527309945113 4179005952472145482458835)
                      ·
                        rfl

theorem cell23_8138585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_8138585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138585 prefixEnd_8138585 := by exact prefixLift 8138585
  have htrace : WordTrace (prefixWord ++ tailWord_8138585) baseStart_8138585 baseEnd_8138585 := by
    simpa [prefixWord, tailWord_8138585, baseEnd_8138585] using wordTrace_append hprefix tailTrace_8138585
  have hstable : (prefixWord ++ tailWord_8138585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138585).length < 2 ^ (prefixWord ++ tailWord_8138585).sum := by decide
  have hdescent : baseEnd_8138585 < baseStart_8138585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138591 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 2, 6]
def baseStart_8138591 : Nat := 118140960795 + 8138591 * 2 ^ 59
def prefixEnd_8138591 : Nat := 4983230072969 + 3 ^ 40 * 8138591 * 2
def baseEnd_8138591 : Nat := 1393003011118690819661269

theorem tailTrace_8138591 : CollatzResearch.WordTrace tailWord_8138591 prefixEnd_8138591 1393003011118690819661269 := by
  unfold tailWord_8138591
  simp only [CollatzResearch.WordTrace]
  refine ⟨296838800058282242527487627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197892533372188161684991751 296838800058282242527487627)
  ·
    refine ⟨445258200087423363791231441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296838800058282242527487627 445258200087423363791231441)
    ·
      refine ⟨333943650065567522843423581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445258200087423363791231441 333943650065567522843423581)
      ·
        refine ⟨125228868774587821066283843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333943650065567522843423581 125228868774587821066283843)
        ·
          refine ⟨187843303161881731599425765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125228868774587821066283843 187843303161881731599425765)
          ·
            refine ⟨35220619342852824674892331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187843303161881731599425765 35220619342852824674892331)
            ·
              refine ⟨52830929014279237012338497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35220619342852824674892331 52830929014279237012338497)
              ·
                refine ⟨39623196760709427759253873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52830929014279237012338497 39623196760709427759253873)
                ·
                  refine ⟨29717397570532070819440405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39623196760709427759253873 29717397570532070819440405)
                  ·
                    refine ⟨1393003011118690819661269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29717397570532070819440405 1393003011118690819661269)
                    ·
                      rfl

theorem cell23_8138591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_8138591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138591 prefixEnd_8138591 := by exact prefixLift 8138591
  have htrace : WordTrace (prefixWord ++ tailWord_8138591) baseStart_8138591 baseEnd_8138591 := by
    simpa [prefixWord, tailWord_8138591, baseEnd_8138591] using wordTrace_append hprefix tailTrace_8138591
  have hstable : (prefixWord ++ tailWord_8138591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138591).length < 2 ^ (prefixWord ++ tailWord_8138591).sum := by decide
  have hdescent : baseEnd_8138591 < baseStart_8138591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138592 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 2, 1, 3]
def baseStart_8138592 : Nat := 118140960795 + 8138592 * 2 ^ 59
def prefixEnd_8138592 : Nat := 4983230072969 + 3 ^ 40 * 8138592 * 2
def baseEnd_8138592 : Nat := 4179009546836726955071303

theorem tailTrace_8138592 : CollatzResearch.WordTrace tailWord_8138592 prefixEnd_8138592 4179009546836726955071303 := by
  unfold tailWord_8138592
  simp only [CollatzResearch.WordTrace]
  refine ⟨148419418265639309849137015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197892557687519079798849353 148419418265639309849137015)
  ·
    refine ⟨222629127398458964773705523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148419418265639309849137015 222629127398458964773705523)
    ·
      refine ⟨333943691097688447160558285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222629127398458964773705523 333943691097688447160558285)
      ·
        refine ⟨125228884161633167685209357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333943691097688447160558285 125228884161633167685209357)
        ·
          refine ⟨46960831560612437881953509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125228884161633167685209357 46960831560612437881953509)
          ·
            refine ⟨8805155917614832102866283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46960831560612437881953509 8805155917614832102866283)
            ·
              refine ⟨13207733876422248154299425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805155917614832102866283 13207733876422248154299425)
              ·
                refine ⟨9905800407316686115724569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13207733876422248154299425 9905800407316686115724569)
                ·
                  refine ⟨7429350305487514586793427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9905800407316686115724569 7429350305487514586793427)
                  ·
                    refine ⟨11144025458231271880190141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429350305487514586793427 11144025458231271880190141)
                    ·
                      refine ⟨4179009546836726955071303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11144025458231271880190141 4179009546836726955071303)
                      ·
                        rfl

theorem cell23_8138592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_8138592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138592 prefixEnd_8138592 := by exact prefixLift 8138592
  have htrace : WordTrace (prefixWord ++ tailWord_8138592) baseStart_8138592 baseEnd_8138592 := by
    simpa [prefixWord, tailWord_8138592, baseEnd_8138592] using wordTrace_append hprefix tailTrace_8138592
  have hstable : (prefixWord ++ tailWord_8138592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138592).length < 2 ^ (prefixWord ++ tailWord_8138592).sum := by decide
  have hdescent : baseEnd_8138592 < baseStart_8138592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_8138601 : Nat := 118140960795 + 8138601 * 2 ^ 59
def prefixEnd_8138601 : Nat := 4983230072969 + 3 ^ 40 * 8138601 * 2
def baseEnd_8138601 : Nat := 4179014168162617419858761

theorem tailTrace_8138601 : CollatzResearch.WordTrace tailWord_8138601 prefixEnd_8138601 4179014168162617419858761 := by
  unfold tailWord_8138601
  simp only [CollatzResearch.WordTrace]
  refine ⟨296839164788246014235351657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197892776525497342823567771 296839164788246014235351657)
  ·
    refine ⟨222629373591184510676513743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296839164788246014235351657 222629373591184510676513743)
    ·
      refine ⟨333944060386776766014770615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222629373591184510676513743 333944060386776766014770615)
      ·
        refine ⟨500916090580165149022155923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333944060386776766014770615 500916090580165149022155923)
        ·
          refine ⟨751374135870247723533233885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500916090580165149022155923 751374135870247723533233885)
          ·
            refine ⟨281765300951342896324962707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751374135870247723533233885 281765300951342896324962707)
            ·
              refine ⟨422647951427014344487444061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281765300951342896324962707 422647951427014344487444061)
              ·
                refine ⟨158492981785130379182791523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422647951427014344487444061 158492981785130379182791523)
                ·
                  refine ⟨237739472677695568774187285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158492981785130379182791523 237739472677695568774187285)
                  ·
                    refine ⟨11144037781766979786290029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 237739472677695568774187285 11144037781766979786290029)
                    ·
                      refine ⟨4179014168162617419858761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11144037781766979786290029 4179014168162617419858761)
                      ·
                        rfl

theorem cell23_8138601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_8138601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138601 prefixEnd_8138601 := by exact prefixLift 8138601
  have htrace : WordTrace (prefixWord ++ tailWord_8138601) baseStart_8138601 baseEnd_8138601 := by
    simpa [prefixWord, tailWord_8138601, baseEnd_8138601] using wordTrace_append hprefix tailTrace_8138601
  have hstable : (prefixWord ++ tailWord_8138601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138601).length < 2 ^ (prefixWord ++ tailWord_8138601).sum := by decide
  have hdescent : baseEnd_8138601 < baseStart_8138601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138655 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 7]
def baseStart_8138655 : Nat := 118140960795 + 8138655 * 2 ^ 59
def prefixEnd_8138655 : Nat := 4983230072969 + 3 ^ 40 * 8138655 * 2
def baseEnd_8138655 : Nat := 464337988457551134287057

theorem tailTrace_8138655 : CollatzResearch.WordTrace tailWord_8138655 prefixEnd_8138655 464337988457551134287057 := by
  unfold tailWord_8138655
  simp only [CollatzResearch.WordTrace]
  refine ⟨296841134330050381457817419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197894089553366920971878279 296841134330050381457817419)
  ·
    refine ⟨445261701495075572186726129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296841134330050381457817419 445261701495075572186726129)
    ·
      refine ⟨333946276121306679140044597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445261701495075572186726129 333946276121306679140044597)
      ·
        refine ⟨31307463386372501169379181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333946276121306679140044597 31307463386372501169379181)
        ·
          refine ⟨11740298769889687938517193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31307463386372501169379181 11740298769889687938517193)
          ·
            refine ⟨8805224077417265953887895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11740298769889687938517193 8805224077417265953887895)
            ·
              refine ⟨13207836116125898930831843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805224077417265953887895 13207836116125898930831843)
              ·
                refine ⟨19811754174188848396247765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207836116125898930831843 19811754174188848396247765)
                ·
                  refine ⟨464337988457551134287057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19811754174188848396247765 464337988457551134287057)
                  ·
                    rfl

theorem cell23_8138655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 7].length) (baseStart_8138655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138655 prefixEnd_8138655 := by exact prefixLift 8138655
  have htrace : WordTrace (prefixWord ++ tailWord_8138655) baseStart_8138655 baseEnd_8138655 := by
    simpa [prefixWord, tailWord_8138655, baseEnd_8138655] using wordTrace_append hprefix tailTrace_8138655
  have hstable : (prefixWord ++ tailWord_8138655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138655).length < 2 ^ (prefixWord ++ tailWord_8138655).sum := by decide
  have hdescent : baseEnd_8138655 < baseStart_8138655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138670 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_8138670 : Nat := 118140960795 + 8138670 * 2 ^ 59
def prefixEnd_8138670 : Nat := 4983230072969 + 3 ^ 40 * 8138670 * 2
def baseEnd_8138670 : Nat := 4179049598327777649895945

theorem tailTrace_8138670 : CollatzResearch.WordTrace tailWord_8138670 prefixEnd_8138670 4179049598327777649895945 := by
  unfold tailWord_8138670
  simp only [CollatzResearch.WordTrace]
  refine ⟨37105210178124504877451683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197894454283330692679742309 37105210178124504877451683)
  ·
    refine ⟨55657815267186757316177525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37105210178124504877451683 55657815267186757316177525)
    ·
      refine ⟨5217920181298758498391643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55657815267186757316177525 5217920181298758498391643)
      ·
        refine ⟨7826880271948137747587465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217920181298758498391643 7826880271948137747587465)
        ·
          refine ⟨5870160203961103310690599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7826880271948137747587465 5870160203961103310690599)
          ·
            refine ⟨8805240305941654966035899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870160203961103310690599 8805240305941654966035899)
            ·
              refine ⟨13207860458912482449053849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805240305941654966035899 13207860458912482449053849)
              ·
                refine ⟨9905895344184361836790387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13207860458912482449053849 9905895344184361836790387)
                ·
                  refine ⟨14858843016276542755185581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905895344184361836790387 14858843016276542755185581)
                  ·
                    refine ⟨5572066131103703533194593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14858843016276542755185581 5572066131103703533194593)
                    ·
                      refine ⟨4179049598327777649895945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572066131103703533194593 4179049598327777649895945)
                      ·
                        rfl

theorem cell23_8138670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_8138670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138670 prefixEnd_8138670 := by exact prefixLift 8138670
  have htrace : WordTrace (prefixWord ++ tailWord_8138670) baseStart_8138670 baseEnd_8138670 := by
    simpa [prefixWord, tailWord_8138670, baseEnd_8138670] using wordTrace_append hprefix tailTrace_8138670
  have hstable : (prefixWord ++ tailWord_8138670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138670).length < 2 ^ (prefixWord ++ tailWord_8138670).sum := by decide
  have hdescent : baseEnd_8138670 < baseStart_8138670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138685 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_8138685 : Nat := 118140960795 + 8138685 * 2 ^ 59
def prefixEnd_8138685 : Nat := 4983230072969 + 3 ^ 40 * 8138685 * 2
def baseEnd_8138685 : Nat := 1393019100179198363736125

theorem tailTrace_8138685 : CollatzResearch.WordTrace tailWord_8138685 prefixEnd_8138685 1393019100179198363736125 := by
  unfold tailWord_8138685
  simp only [CollatzResearch.WordTrace]
  refine ⟨296842228519941696581409509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197894819013294464387606339 296842228519941696581409509)
  ·
    refine ⟨55657917847489068109014283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296842228519941696581409509 55657917847489068109014283)
    ·
      refine ⟨83486876771233602163521425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55657917847489068109014283 83486876771233602163521425)
      ·
        refine ⟨62615157578425201622641069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83486876771233602163521425 62615157578425201622641069)
        ·
          refine ⟨23480684091909450608490401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62615157578425201622641069 23480684091909450608490401)
          ·
            refine ⟨17610513068932087956367801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23480684091909450608490401 17610513068932087956367801)
            ·
              refine ⟨13207884801699065967275851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17610513068932087956367801 13207884801699065967275851)
              ·
                refine ⟨19811827202548598950913777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207884801699065967275851 19811827202548598950913777)
                ·
                  refine ⟨14858870401911449213185333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19811827202548598950913777 14858870401911449213185333)
                  ·
                    refine ⟨1393019100179198363736125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14858870401911449213185333 1393019100179198363736125)
                    ·
                      rfl

theorem cell23_8138685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_8138685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138685 prefixEnd_8138685 := by exact prefixLift 8138685
  have htrace : WordTrace (prefixWord ++ tailWord_8138685) baseStart_8138685 baseEnd_8138685 := by
    simpa [prefixWord, tailWord_8138685, baseEnd_8138685] using wordTrace_append hprefix tailTrace_8138685
  have hstable : (prefixWord ++ tailWord_8138685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138685).length < 2 ^ (prefixWord ++ tailWord_8138685).sum := by decide
  have hdescent : baseEnd_8138685 < baseStart_8138685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138691 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_8138691 : Nat := 118140960795 + 8138691 * 2 ^ 59
def prefixEnd_8138691 : Nat := 4983230072969 + 3 ^ 40 * 8138691 * 2
def baseEnd_8138691 : Nat := 4179060381421522067733347

theorem tailTrace_8138691 : CollatzResearch.WordTrace tailWord_8138691 prefixEnd_8138691 4179060381421522067733347 := by
  unfold tailWord_8138691
  simp only [CollatzResearch.WordTrace]
  refine ⟨296842447357919959606127927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197894964905279973070751951 296842447357919959606127927)
  ·
    refine ⟨445263671036879939409191891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296842447357919959606127927 445263671036879939409191891)
    ·
      refine ⟨667895506555319909113787837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445263671036879939409191891 667895506555319909113787837)
      ·
        refine ⟨250460814958244965917670439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667895506555319909113787837 250460814958244965917670439)
        ·
          refine ⟨375691222437367448876505659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250460814958244965917670439 375691222437367448876505659)
          ·
            refine ⟨563536833656051173314758489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375691222437367448876505659 563536833656051173314758489)
            ·
              refine ⟨422652625242038379986068867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563536833656051173314758489 422652625242038379986068867)
              ·
                refine ⟨633978937863057569979103301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422652625242038379986068867 633978937863057569979103301)
                ·
                  refine ⟨118871050849323294371081869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 633978937863057569979103301 118871050849323294371081869)
                  ·
                    refine ⟨44576644068496235389155701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118871050849323294371081869 44576644068496235389155701)
                    ·
                      refine ⟨4179060381421522067733347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44576644068496235389155701 4179060381421522067733347)
                      ·
                        rfl

theorem cell23_8138691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_8138691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138691 prefixEnd_8138691 := by exact prefixLift 8138691
  have htrace : WordTrace (prefixWord ++ tailWord_8138691) baseStart_8138691 baseEnd_8138691 := by
    simpa [prefixWord, tailWord_8138691, baseEnd_8138691] using wordTrace_append hprefix tailTrace_8138691
  have hstable : (prefixWord ++ tailWord_8138691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138691).length < 2 ^ (prefixWord ++ tailWord_8138691).sum := by decide
  have hdescent : baseEnd_8138691 < baseStart_8138691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138706 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_8138706 : Nat := 118140960795 + 8138706 * 2 ^ 59
def prefixEnd_8138706 : Nat := 4983230072969 + 3 ^ 40 * 8138706 * 2
def baseEnd_8138706 : Nat := 464340898181259945449531

theorem tailTrace_8138706 : CollatzResearch.WordTrace tailWord_8138706 prefixEnd_8138706 464340898181259945449531 := by
  unfold tailWord_8138706
  simp only [CollatzResearch.WordTrace]
  refine ⟨74210748613216404291980993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197895329635243744778615981 74210748613216404291980993)
  ·
    refine ⟨55658061459912303218985745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74210748613216404291980993 55658061459912303218985745)
    ·
      refine ⟨41743546094934227414239309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55658061459912303218985745 41743546094934227414239309)
      ·
        refine ⟨15653829785600335280339741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41743546094934227414239309 15653829785600335280339741)
        ·
          refine ⟨5870186169600125730127403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15653829785600335280339741 5870186169600125730127403)
          ·
            refine ⟨8805279254400188595191105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870186169600125730127403 8805279254400188595191105)
            ·
              refine ⟨6603959440800141446393329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8805279254400188595191105 6603959440800141446393329)
              ·
                refine ⟨4952969580600106084794997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6603959440800141446393329 4952969580600106084794997)
                ·
                  refine ⟨464340898181259945449531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4952969580600106084794997 464340898181259945449531)
                  ·
                    rfl

theorem cell23_8138706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_8138706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138706 prefixEnd_8138706 := by exact prefixLift 8138706
  have htrace : WordTrace (prefixWord ++ tailWord_8138706) baseStart_8138706 baseEnd_8138706 := by
    simpa [prefixWord, tailWord_8138706, baseEnd_8138706] using wordTrace_append hprefix tailTrace_8138706
  have hstable : (prefixWord ++ tailWord_8138706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138706).length < 2 ^ (prefixWord ++ tailWord_8138706).sum := by decide
  have hdescent : baseEnd_8138706 < baseStart_8138706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138708 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_8138708 : Nat := 118140960795 + 8138708 * 2 ^ 59
def prefixEnd_8138708 : Nat := 4983230072969 + 3 ^ 40 * 8138708 * 2
def baseEnd_8138708 : Nat := 4179069110592648501220769

theorem tailTrace_8138708 : CollatzResearch.WordTrace tailWord_8138708 prefixEnd_8138708 4179069110592648501220769 := by
  unfold tailWord_8138708
  simp only [CollatzResearch.WordTrace]
  refine ⟨148421533699429185754748389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197895378265905581006331185 148421533699429185754748389)
  ·
    refine ⟨27829037568642972329015323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148421533699429185754748389 27829037568642972329015323)
    ·
      refine ⟨41743556352964458493522985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27829037568642972329015323 41743556352964458493522985)
      ·
        refine ⟨31307667264723343870142239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41743556352964458493522985 31307667264723343870142239)
        ·
          refine ⟨46961500897085015805213359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31307667264723343870142239 46961500897085015805213359)
          ·
            refine ⟨70442251345627523707820039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46961500897085015805213359 70442251345627523707820039)
            ·
              refine ⟨105663377018441285561730059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70442251345627523707820039 105663377018441285561730059)
              ·
                refine ⟨158495065527661928342595089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105663377018441285561730059 158495065527661928342595089)
                ·
                  refine ⟨118871299145746446256946317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158495065527661928342595089 118871299145746446256946317)
                  ·
                    refine ⟨44576737179654917346354869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118871299145746446256946317 44576737179654917346354869)
                    ·
                      refine ⟨4179069110592648501220769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44576737179654917346354869 4179069110592648501220769)
                      ·
                        rfl

theorem cell23_8138708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_8138708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138708 prefixEnd_8138708 := by exact prefixLift 8138708
  have htrace : WordTrace (prefixWord ++ tailWord_8138708) baseStart_8138708 baseEnd_8138708 := by
    simpa [prefixWord, tailWord_8138708, baseEnd_8138708] using wordTrace_append hprefix tailTrace_8138708
  have hstable : (prefixWord ++ tailWord_8138708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138708).length < 2 ^ (prefixWord ++ tailWord_8138708).sum := by decide
  have hdescent : baseEnd_8138708 < baseStart_8138708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138742 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_8138742 : Nat := 118140960795 + 8138742 * 2 ^ 59
def prefixEnd_8138742 : Nat := 4983230072969 + 3 ^ 40 * 8138742 * 2
def baseEnd_8138742 : Nat := 4179086568934901368195613

theorem tailTrace_8138742 : CollatzResearch.WordTrace tailWord_8138742 prefixEnd_8138742 4179086568934901368195613 := by
  unfold tailWord_8138742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18552769217545949707264655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197896204987156796877489653 18552769217545949707264655)
  ·
    refine ⟨27829153826318924560896983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18552769217545949707264655 27829153826318924560896983)
    ·
      refine ⟨41743730739478386841345475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27829153826318924560896983 41743730739478386841345475)
      ·
        refine ⟨62615596109217580262018213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41743730739478386841345475 62615596109217580262018213)
        ·
          refine ⟨11740424270478296299128415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62615596109217580262018213 11740424270478296299128415)
          ·
            refine ⟨17610636405717444448692623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740424270478296299128415 17610636405717444448692623)
            ·
              refine ⟨26415954608576166673038935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17610636405717444448692623 26415954608576166673038935)
              ·
                refine ⟨39623931912864250009558403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26415954608576166673038935 39623931912864250009558403)
                ·
                  refine ⟨59435897869296375014337605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39623931912864250009558403 59435897869296375014337605)
                  ·
                    refine ⟨11144230850493070315188301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59435897869296375014337605 11144230850493070315188301)
                    ·
                      refine ⟨4179086568934901368195613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11144230850493070315188301 4179086568934901368195613)
                      ·
                        rfl

theorem cell23_8138742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_8138742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138742 prefixEnd_8138742 := by exact prefixLift 8138742
  have htrace : WordTrace (prefixWord ++ tailWord_8138742) baseStart_8138742 baseEnd_8138742 := by
    simpa [prefixWord, tailWord_8138742, baseEnd_8138742] using wordTrace_append hprefix tailTrace_8138742
  have hstable : (prefixWord ++ tailWord_8138742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138742).length < 2 ^ (prefixWord ++ tailWord_8138742).sum := by decide
  have hdescent : baseEnd_8138742 < baseStart_8138742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138762 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_8138762 : Nat := 118140960795 + 8138762 * 2 ^ 59
def prefixEnd_8138762 : Nat := 4983230072969 + 3 ^ 40 * 8138762 * 2
def baseEnd_8138762 : Nat := 464344093171999032216169

theorem tailTrace_8138762 : CollatzResearch.WordTrace tailWord_8138762 prefixEnd_8138762 464344093171999032216169 := by
  unfold tailWord_8138762
  simp only [CollatzResearch.WordTrace]
  refine ⟨74211259235165684682990635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197896691293775159154641693 74211259235165684682990635)
  ·
    refine ⟨111316888852748527024485953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74211259235165684682990635 111316888852748527024485953)
    ·
      refine ⟨83487666639561395268364465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111316888852748527024485953 83487666639561395268364465)
      ·
        refine ⟨62615749979671046451273349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83487666639561395268364465 62615749979671046451273349)
        ·
          refine ⟨11740453121188321209613753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62615749979671046451273349 11740453121188321209613753)
          ·
            refine ⟨8805339840891240907210315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11740453121188321209613753 8805339840891240907210315)
            ·
              refine ⟨13208009761336861360815473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805339840891240907210315 13208009761336861360815473)
              ·
                refine ⟨9906007321002646020611605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13208009761336861360815473 9906007321002646020611605)
                ·
                  refine ⟨464344093171999032216169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9906007321002646020611605 464344093171999032216169)
                  ·
                    rfl

theorem cell23_8138762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_8138762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138762 prefixEnd_8138762 := by exact prefixLift 8138762
  have htrace : WordTrace (prefixWord ++ tailWord_8138762) baseStart_8138762 baseEnd_8138762 := by
    simpa [prefixWord, tailWord_8138762, baseEnd_8138762] using wordTrace_append hprefix tailTrace_8138762
  have hstable : (prefixWord ++ tailWord_8138762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138762).length < 2 ^ (prefixWord ++ tailWord_8138762).sum := by decide
  have hdescent : baseEnd_8138762 < baseStart_8138762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138805 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_8138805 : Nat := 118140960795 + 8138805 * 2 ^ 59
def prefixEnd_8138805 : Nat := 4983230072969 + 3 ^ 40 * 8138805 * 2
def baseEnd_8138805 : Nat := 1393039639405378207235941

theorem tailTrace_8138805 : CollatzResearch.WordTrace tailWord_8138805 prefixEnd_8138805 1393039639405378207235941 := by
  unfold tailWord_8138805
  simp only [CollatzResearch.WordTrace]
  refine ⟨296846605279506957075777869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197897736853004638050518579 296846605279506957075777869)
  ·
    refine ⟨111317476979815108903416701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296846605279506957075777869 111317476979815108903416701)
    ·
      refine ⟨41744053867430665838781263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111317476979815108903416701 41744053867430665838781263)
      ·
        refine ⟨62616080801145998758171895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41744053867430665838781263 62616080801145998758171895)
        ·
          refine ⟨93924121201718998137257843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62616080801145998758171895 93924121201718998137257843)
          ·
            refine ⟨140886181802578497205886765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93924121201718998137257843 140886181802578497205886765)
            ·
              refine ⟨52832318175966936452207537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140886181802578497205886765 52832318175966936452207537)
              ·
                refine ⟨39624238631975202339155653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52832318175966936452207537 39624238631975202339155653)
                ·
                  refine ⟨7429544743495350438591685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39624238631975202339155653 7429544743495350438591685)
                  ·
                    refine ⟨1393039639405378207235941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429544743495350438591685 1393039639405378207235941)
                    ·
                      rfl

theorem cell23_8138805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_8138805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138805 prefixEnd_8138805 := by exact prefixLift 8138805
  have htrace : WordTrace (prefixWord ++ tailWord_8138805) baseStart_8138805 baseEnd_8138805 := by
    simpa [prefixWord, tailWord_8138805, baseEnd_8138805] using wordTrace_append hprefix tailTrace_8138805
  have hstable : (prefixWord ++ tailWord_8138805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138805).length < 2 ^ (prefixWord ++ tailWord_8138805).sum := by decide
  have hdescent : baseEnd_8138805 < baseStart_8138805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138846 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_8138846 : Nat := 118140960795 + 8138846 * 2 ^ 59
def prefixEnd_8138846 : Nat := 4983230072969 + 3 ^ 40 * 8138846 * 2
def baseEnd_8138846 : Nat := 4179139970922968961295135

theorem tailTrace_8138846 : CollatzResearch.WordTrace tailWord_8138846 prefixEnd_8138846 4179139970922968961295135 := by
  unfold tailWord_8138846
  simp only [CollatzResearch.WordTrace]
  refine ⟨37106012584044802634752549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197898733781572280718680261 37106012584044802634752549)
  ·
    refine ⟨6957377359508400494016103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37106012584044802634752549 6957377359508400494016103)
    ·
      refine ⟨10436066039262600741024155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6957377359508400494016103 10436066039262600741024155)
      ·
        refine ⟨15654099058893901111536233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10436066039262600741024155 15654099058893901111536233)
        ·
          refine ⟨11740574294170425833652175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15654099058893901111536233 11740574294170425833652175)
          ·
            refine ⟨17610861441255638750478263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740574294170425833652175 17610861441255638750478263)
            ·
              refine ⟨26416292161883458125717395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17610861441255638750478263 26416292161883458125717395)
              ·
                refine ⟨39624438242825187188576093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26416292161883458125717395 39624438242825187188576093)
                ·
                  refine ⟨14859164341059445195716035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39624438242825187188576093 14859164341059445195716035)
                  ·
                    refine ⟨22288746511589167793574053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14859164341059445195716035 22288746511589167793574053)
                    ·
                      refine ⟨4179139970922968961295135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22288746511589167793574053 4179139970922968961295135)
                      ·
                        rfl

theorem cell23_8138846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_8138846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138846 prefixEnd_8138846 := by exact prefixLift 8138846
  have htrace : WordTrace (prefixWord ++ tailWord_8138846) baseStart_8138846 baseEnd_8138846 := by
    simpa [prefixWord, tailWord_8138846, baseEnd_8138846] using wordTrace_append hprefix tailTrace_8138846
  have hstable : (prefixWord ++ tailWord_8138846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138846).length < 2 ^ (prefixWord ++ tailWord_8138846).sum := by decide
  have hdescent : baseEnd_8138846 < baseStart_8138846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138862 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_8138862 : Nat := 118140960795 + 8138862 * 2 ^ 59
def prefixEnd_8138862 : Nat := 4983230072969 + 3 ^ 40 * 8138862 * 2
def baseEnd_8138862 : Nat := 4179148186613440898695061

theorem tailTrace_8138862 : CollatzResearch.WordTrace tailWord_8138862 prefixEnd_8138862 4179148186613440898695061 := by
  unfold tailWord_8138862
  simp only [CollatzResearch.WordTrace]
  refine ⟨37106085530037556976325355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197899122826866970540401893 37106085530037556976325355)
  ·
    refine ⟨55659128295056335464488033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37106085530037556976325355 55659128295056335464488033)
    ·
      refine ⟨41744346221292251598366025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55659128295056335464488033 41744346221292251598366025)
      ·
        refine ⟨31308259665969188698774519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41744346221292251598366025 31308259665969188698774519)
        ·
          refine ⟨46962389498953783048161779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31308259665969188698774519 46962389498953783048161779)
          ·
            refine ⟨70443584248430674572242669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46962389498953783048161779 70443584248430674572242669)
            ·
              refine ⟨26416344093161502964591001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70443584248430674572242669 26416344093161502964591001)
              ·
                refine ⟨19812258069871127223443251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26416344093161502964591001 19812258069871127223443251)
                ·
                  refine ⟨29718387104806690835164877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19812258069871127223443251 29718387104806690835164877)
                  ·
                    refine ⟨11144395164302509063186829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29718387104806690835164877 11144395164302509063186829)
                    ·
                      refine ⟨4179148186613440898695061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11144395164302509063186829 4179148186613440898695061)
                      ·
                        rfl

theorem cell23_8138862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_8138862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138862 prefixEnd_8138862 := by exact prefixLift 8138862
  have htrace : WordTrace (prefixWord ++ tailWord_8138862) baseStart_8138862 baseEnd_8138862 := by
    simpa [prefixWord, tailWord_8138862, baseEnd_8138862] using wordTrace_append hprefix tailTrace_8138862
  have hstable : (prefixWord ++ tailWord_8138862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138862).length < 2 ^ (prefixWord ++ tailWord_8138862).sum := by decide
  have hdescent : baseEnd_8138862 < baseStart_8138862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138885 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_8138885 : Nat := 118140960795 + 8138885 * 2 ^ 59
def prefixEnd_8138885 : Nat := 4983230072969 + 3 ^ 40 * 8138885 * 2
def baseEnd_8138885 : Nat := 4179159996668494308707455

theorem tailTrace_8138885 : CollatzResearch.WordTrace tailWord_8138885 prefixEnd_8138885 4179159996668494308707455 := by
  unfold tailWord_8138885
  simp only [CollatzResearch.WordTrace]
  refine ⟨296849523119217130738690109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197899682079478087159126739 296849523119217130738690109)
  ·
    refine ⟨111318571169706424027008791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296849523119217130738690109 111318571169706424027008791)
    ·
      refine ⟨166977856754559636040513187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111318571169706424027008791 166977856754559636040513187)
      ·
        refine ⟨250466785131839454060769781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166977856754559636040513187 250466785131839454060769781)
        ·
          refine ⟨23481261106109948818197167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250466785131839454060769781 23481261106109948818197167)
          ·
            refine ⟨35221891659164923227295751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23481261106109948818197167 35221891659164923227295751)
            ·
              refine ⟨52832837488747384840943627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35221891659164923227295751 52832837488747384840943627)
              ·
                refine ⟨79249256233121077261415441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52832837488747384840943627 79249256233121077261415441)
                ·
                  refine ⟨59436942174840807946061581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79249256233121077261415441 59436942174840807946061581)
                  ·
                    refine ⟨22288853315565302979773093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59436942174840807946061581 22288853315565302979773093)
                    ·
                      refine ⟨4179159996668494308707455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22288853315565302979773093 4179159996668494308707455)
                      ·
                        rfl

theorem cell23_8138885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_8138885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138885 prefixEnd_8138885 := by exact prefixLift 8138885
  have htrace : WordTrace (prefixWord ++ tailWord_8138885) baseStart_8138885 baseEnd_8138885 := by
    simpa [prefixWord, tailWord_8138885, baseEnd_8138885] using wordTrace_append hprefix tailTrace_8138885
  have hstable : (prefixWord ++ tailWord_8138885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138885).length < 2 ^ (prefixWord ++ tailWord_8138885).sum := by decide
  have hdescent : baseEnd_8138885 < baseStart_8138885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138989 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_8138989 : Nat := 118140960795 + 8138989 * 2 ^ 59
def prefixEnd_8138989 : Nat := 4983230072969 + 3 ^ 40 * 8138989 * 2
def baseEnd_8138989 : Nat := 1393071132885520633935659

theorem tailTrace_8138989 : CollatzResearch.WordTrace tailWord_8138989 prefixEnd_8138989 1393071132885520633935659 := by
  unfold tailWord_8138989
  simp only [CollatzResearch.WordTrace]
  refine ⟨296853316310840356500476021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197902210873893571000317347 296853316310840356500476021)
  ·
    refine ⟨27829998404141283421919627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296853316310840356500476021 27829998404141283421919627)
    ·
      refine ⟨41744997606211925132879441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27829998404141283421919627 41744997606211925132879441)
      ·
        refine ⟨31308748204658943849659581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41744997606211925132879441 31308748204658943849659581)
        ·
          refine ⟨11740780576747103943622343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31308748204658943849659581 11740780576747103943622343)
          ·
            refine ⟨17611170865120655915433515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740780576747103943622343 17611170865120655915433515)
            ·
              refine ⟨26416756297680983873150273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17611170865120655915433515 26416756297680983873150273)
              ·
                refine ⟨19812567223260737904862705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26416756297680983873150273 19812567223260737904862705)
                ·
                  refine ⟨14859425417445553428647029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19812567223260737904862705 14859425417445553428647029)
                  ·
                    refine ⟨1393071132885520633935659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14859425417445553428647029 1393071132885520633935659)
                    ·
                      rfl

theorem cell23_8138989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_8138989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138989 prefixEnd_8138989 := by exact prefixLift 8138989
  have htrace : WordTrace (prefixWord ++ tailWord_8138989) baseStart_8138989 baseEnd_8138989 := by
    simpa [prefixWord, tailWord_8138989, baseEnd_8138989] using wordTrace_append hprefix tailTrace_8138989
  have hstable : (prefixWord ++ tailWord_8138989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138989).length < 2 ^ (prefixWord ++ tailWord_8138989).sum := by decide
  have hdescent : baseEnd_8138989 < baseStart_8138989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8138992 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 4, 4, 2]
def baseStart_8138992 : Nat := 118140960795 + 8138992 * 2 ^ 59
def prefixEnd_8138992 : Nat := 4983230072969 + 3 ^ 40 * 8138992 * 2
def baseEnd_8138992 : Nat := 4179214939098525390069463

theorem tailTrace_8138992 : CollatzResearch.WordTrace tailWord_8138992 prefixEnd_8138992 4179214939098525390069463 := by
  unfold tailWord_8138992
  simp only [CollatzResearch.WordTrace]
  refine ⟨148426712864914744006417615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197902283819886325341890153 148426712864914744006417615)
  ·
    refine ⟨222640069297372116009626423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148426712864914744006417615 222640069297372116009626423)
    ·
      refine ⟨333960103946058174014439635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222640069297372116009626423 333960103946058174014439635)
      ·
        refine ⟨500940155919087261021659453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333960103946058174014439635 500940155919087261021659453)
        ·
          refine ⟨187852558469657722883122295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500940155919087261021659453 187852558469657722883122295)
          ·
            refine ⟨281778837704486584324683443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187852558469657722883122295 281778837704486584324683443)
            ·
              refine ⟨422668256556729876487025165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281778837704486584324683443 422668256556729876487025165)
              ·
                refine ⟨158500596208773703682634437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422668256556729876487025165 158500596208773703682634437)
                ·
                  refine ⟨29718861789145069440493957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158500596208773703682634437 29718861789145069440493957)
                  ·
                    refine ⟨5572286585464700520092617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29718861789145069440493957 5572286585464700520092617)
                    ·
                      refine ⟨4179214939098525390069463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572286585464700520092617 4179214939098525390069463)
                      ·
                        rfl

theorem cell23_8138992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 4, 2].length) (baseStart_8138992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8138992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8138992 prefixEnd_8138992 := by exact prefixLift 8138992
  have htrace : WordTrace (prefixWord ++ tailWord_8138992) baseStart_8138992 baseEnd_8138992 := by
    simpa [prefixWord, tailWord_8138992, baseEnd_8138992] using wordTrace_append hprefix tailTrace_8138992
  have hstable : (prefixWord ++ tailWord_8138992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8138992).length < 2 ^ (prefixWord ++ tailWord_8138992).sum := by decide
  have hdescent : baseEnd_8138992 < baseStart_8138992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8138992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139005 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_8139005 : Nat := 118140960795 + 8139005 * 2 ^ 59
def prefixEnd_8139005 : Nat := 4983230072969 + 3 ^ 40 * 8139005 * 2
def baseEnd_8139005 : Nat := 4179221614347033839206903

theorem tailTrace_8139005 : CollatzResearch.WordTrace tailWord_8139005 prefixEnd_8139005 4179221614347033839206903 := by
  unfold tailWord_8139005
  simp only [CollatzResearch.WordTrace]
  refine ⟨296853899878782391233058469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197902599919188260822038979 296853899878782391233058469)
  ·
    refine ⟨55660106227271698356198463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296853899878782391233058469 55660106227271698356198463)
    ·
      refine ⟨83490159340907547534297695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55660106227271698356198463 83490159340907547534297695)
      ·
        refine ⟨125235239011361321301446543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83490159340907547534297695 125235239011361321301446543)
        ·
          refine ⟨187852858517041981952169815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125235239011361321301446543 187852858517041981952169815)
          ·
            refine ⟨281779287775562972928254723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187852858517041981952169815 281779287775562972928254723)
            ·
              refine ⟨422668931663344459392382085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281779287775562972928254723 422668931663344459392382085)
              ·
                refine ⟨79250424686877086136071641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422668931663344459392382085 79250424686877086136071641)
                ·
                  refine ⟨59437818515157814602053731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79250424686877086136071641 59437818515157814602053731)
                  ·
                    refine ⟨89156727772736721903080597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59437818515157814602053731 89156727772736721903080597)
                    ·
                      refine ⟨4179221614347033839206903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89156727772736721903080597 4179221614347033839206903)
                      ·
                        rfl

theorem cell23_8139005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_8139005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139005 prefixEnd_8139005 := by exact prefixLift 8139005
  have htrace : WordTrace (prefixWord ++ tailWord_8139005) baseStart_8139005 baseEnd_8139005 := by
    simpa [prefixWord, tailWord_8139005, baseEnd_8139005] using wordTrace_append hprefix tailTrace_8139005
  have hstable : (prefixWord ++ tailWord_8139005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139005).length < 2 ^ (prefixWord ++ tailWord_8139005).sum := by decide
  have hdescent : baseEnd_8139005 < baseStart_8139005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139059 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 3]
def baseStart_8139059 : Nat := 118140960795 + 8139059 * 2 ^ 59
def prefixEnd_8139059 : Nat := 4983230072969 + 3 ^ 40 * 8139059 * 2
def baseEnd_8139059 : Nat := 4179249342302376627931655

theorem tailTrace_8139059 : CollatzResearch.WordTrace tailWord_8139059 prefixEnd_8139059 4179249342302376627931655 := by
  unfold tailWord_8139059
  simp only [CollatzResearch.WordTrace]
  refine ⟨296855869420586758455524231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197903912947057838970349487 296855869420586758455524231)
  ·
    refine ⟨445283804130880137683286347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296855869420586758455524231 445283804130880137683286347)
    ·
      refine ⟨667925706196320206524929521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445283804130880137683286347 667925706196320206524929521)
      ·
        refine ⟨500944279647240154893697141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667925706196320206524929521 500944279647240154893697141)
        ·
          refine ⟨46963526216928764521284107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 500944279647240154893697141 46963526216928764521284107)
          ·
            refine ⟨70445289325393146781926161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46963526216928764521284107 70445289325393146781926161)
            ·
              refine ⟨52833966994044860086444621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70445289325393146781926161 52833966994044860086444621)
              ·
                refine ⟨19812737622766822532416733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52833966994044860086444621 19812737622766822532416733)
                ·
                  refine ⟨7429776608537558449656275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19812737622766822532416733 7429776608537558449656275)
                  ·
                    refine ⟨11144664912806337674484413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429776608537558449656275 11144664912806337674484413)
                    ·
                      refine ⟨4179249342302376627931655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11144664912806337674484413 4179249342302376627931655)
                      ·
                        rfl

theorem cell23_8139059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_8139059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139059 prefixEnd_8139059 := by exact prefixLift 8139059
  have htrace : WordTrace (prefixWord ++ tailWord_8139059) baseStart_8139059 baseEnd_8139059 := by
    simpa [prefixWord, tailWord_8139059, baseEnd_8139059] using wordTrace_append hprefix tailTrace_8139059
  have hstable : (prefixWord ++ tailWord_8139059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139059).length < 2 ^ (prefixWord ++ tailWord_8139059).sum := by decide
  have hdescent : baseEnd_8139059 < baseStart_8139059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139109 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_8139109 : Nat := 118140960795 + 8139109 * 2 ^ 59
def prefixEnd_8139109 : Nat := 4983230072969 + 3 ^ 40 * 8139109 * 2
def baseEnd_8139109 : Nat := 1393091672111700477435475

theorem tailTrace_8139109 : CollatzResearch.WordTrace tailWord_8139109 prefixEnd_8139109 1393091672111700477435475 := by
  unfold tailWord_8139109
  simp only [CollatzResearch.WordTrace]
  refine ⟨296857693070405616994844381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197905128713603744663229587 296857693070405616994844381)
  ·
    refine ⟨111321634901402106373066643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296857693070405616994844381 111321634901402106373066643)
    ·
      refine ⟨166982452352103159559599965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111321634901402106373066643 166982452352103159559599965)
      ·
        refine ⟨62618419632038684834849987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166982452352103159559599965 62618419632038684834849987)
        ·
          refine ⟨93927629448058027252274981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62618419632038684834849987 93927629448058027252274981)
          ·
            refine ⟨17611430521510880109801559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93927629448058027252274981 17611430521510880109801559)
            ·
              refine ⟨26417145782266320164702339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17611430521510880109801559 26417145782266320164702339)
              ·
                refine ⟨39625718673399480247053509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26417145782266320164702339 39625718673399480247053509)
                ·
                  refine ⟨7429822251262402546322533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39625718673399480247053509 7429822251262402546322533)
                  ·
                    refine ⟨1393091672111700477435475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429822251262402546322533 1393091672111700477435475)
                    ·
                      rfl

theorem cell23_8139109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_8139109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139109 prefixEnd_8139109 := by exact prefixLift 8139109
  have htrace : WordTrace (prefixWord ++ tailWord_8139109) baseStart_8139109 baseEnd_8139109 := by
    simpa [prefixWord, tailWord_8139109, baseEnd_8139109] using wordTrace_append hprefix tailTrace_8139109
  have hstable : (prefixWord ++ tailWord_8139109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139109).length < 2 ^ (prefixWord ++ tailWord_8139109).sum := by decide
  have hdescent : baseEnd_8139109 < baseStart_8139109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139156 : List Nat := [2, 4, 2, 1, 4, 1, 9]
def baseStart_8139156 : Nat := 118140960795 + 8139156 * 2 ^ 59
def prefixEnd_8139156 : Nat := 4983230072969 + 3 ^ 40 * 8139156 * 2
def baseEnd_8139156 : Nat := 51596285801553861091589

theorem tailTrace_8139156 : CollatzResearch.WordTrace tailWord_8139156 prefixEnd_8139156 51596285801553861091589 := by
  unfold tailWord_8139156
  simp only [CollatzResearch.WordTrace]
  refine ⟨148429703650617672010902661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197906271534156896014536881 148429703650617672010902661)
  ·
    refine ⟨27830569434490813502044249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148429703650617672010902661 27830569434490813502044249)
    ·
      refine ⟨20872927075868110126533187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27830569434490813502044249 20872927075868110126533187)
      ·
        refine ⟨31309390613802165189799781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20872927075868110126533187 31309390613802165189799781)
        ·
          refine ⟨5870510740087905973087459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31309390613802165189799781 5870510740087905973087459)
          ·
            refine ⟨8805766110131858959631189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870510740087905973087459 8805766110131858959631189)
            ·
              refine ⟨51596285801553861091589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8805766110131858959631189 51596285801553861091589)
              ·
                rfl

theorem cell23_8139156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 9].length) (baseStart_8139156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139156 prefixEnd_8139156 := by exact prefixLift 8139156
  have htrace : WordTrace (prefixWord ++ tailWord_8139156) baseStart_8139156 baseEnd_8139156 := by
    simpa [prefixWord, tailWord_8139156, baseEnd_8139156] using wordTrace_append hprefix tailTrace_8139156
  have hstable : (prefixWord ++ tailWord_8139156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139156).length < 2 ^ (prefixWord ++ tailWord_8139156).sum := by decide
  have hdescent : baseEnd_8139156 < baseStart_8139156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139193 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 1, 3, 2]
def baseStart_8139193 : Nat := 118140960795 + 8139193 * 2 ^ 59
def prefixEnd_8139193 : Nat := 4983230072969 + 3 ^ 40 * 8139193 * 2
def baseEnd_8139193 : Nat := 4179318148710079103656039

theorem tailTrace_8139193 : CollatzResearch.WordTrace tailWord_8139193 prefixEnd_8139193 4179318148710079103656039 := by
  unfold tailWord_8139193
  simp only [CollatzResearch.WordTrace]
  refine ⟨296860756802101299340902233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197907171201400866227268155 296860756802101299340902233)
  ·
    refine ⟨222645567601575974505676675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296860756802101299340902233 222645567601575974505676675)
    ·
      refine ⟨333968351402363961758515013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222645567601575974505676675 333968351402363961758515013)
      ·
        refine ⟨62619065887943242829721565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333968351402363961758515013 62619065887943242829721565)
        ·
          refine ⟨23482149707978716061145587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62619065887943242829721565 23482149707978716061145587)
          ·
            refine ⟨35223224561968074091718381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23482149707978716061145587 35223224561968074091718381)
            ·
              refine ⟨13208709210738027784394393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35223224561968074091718381 13208709210738027784394393)
              ·
                refine ⟨9906531908053520838295795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13208709210738027784394393 9906531908053520838295795)
                ·
                  refine ⟨14859797862080281257443693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9906531908053520838295795 14859797862080281257443693)
                  ·
                    refine ⟨5572424198280105471541385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14859797862080281257443693 5572424198280105471541385)
                    ·
                      refine ⟨4179318148710079103656039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572424198280105471541385 4179318148710079103656039)
                      ·
                        rfl

theorem cell23_8139193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_8139193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139193 prefixEnd_8139193 := by exact prefixLift 8139193
  have htrace : WordTrace (prefixWord ++ tailWord_8139193) baseStart_8139193 baseEnd_8139193 := by
    simpa [prefixWord, tailWord_8139193, baseEnd_8139193] using wordTrace_append hprefix tailTrace_8139193
  have hstable : (prefixWord ++ tailWord_8139193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139193).length < 2 ^ (prefixWord ++ tailWord_8139193).sum := by decide
  have hdescent : baseEnd_8139193 < baseStart_8139193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139229 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 7]
def baseStart_8139229 : Nat := 118140960795 + 8139229 * 2 ^ 59
def prefixEnd_8139229 : Nat := 4983230072969 + 3 ^ 40 * 8139229 * 2
def baseEnd_8139229 : Nat := 464370737112626773645097

theorem tailTrace_8139229 : CollatzResearch.WordTrace tailWord_8139229 prefixEnd_8139229 464370737112626773645097 := by
  unfold tailWord_8139229
  simp only [CollatzResearch.WordTrace]
  refine ⟨296862069829970877489212741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197908046553313918326141827 296862069829970877489212741)
  ·
    refine ⟨55661638093119539529227389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296862069829970877489212741 55661638093119539529227389)
    ·
      refine ⟨20873114284919827323460271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55661638093119539529227389 20873114284919827323460271)
      ·
        refine ⟨31309671427379740985190407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20873114284919827323460271 31309671427379740985190407)
        ·
          refine ⟨46964507141069611477785611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31309671427379740985190407 46964507141069611477785611)
          ·
            refine ⟨70446760711604417216678417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46964507141069611477785611 70446760711604417216678417)
            ·
              refine ⟨52835070533703312912508813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70446760711604417216678417 52835070533703312912508813)
              ·
                refine ⟨19813151450138742342190805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52835070533703312912508813 19813151450138742342190805)
                ·
                  refine ⟨464370737112626773645097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19813151450138742342190805 464370737112626773645097)
                  ·
                    rfl

theorem cell23_8139229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_8139229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139229 prefixEnd_8139229 := by exact prefixLift 8139229
  have htrace : WordTrace (prefixWord ++ tailWord_8139229) baseStart_8139229 baseEnd_8139229 := by
    simpa [prefixWord, tailWord_8139229, baseEnd_8139229] using wordTrace_append hprefix tailTrace_8139229
  have hstable : (prefixWord ++ tailWord_8139229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139229).length < 2 ^ (prefixWord ++ tailWord_8139229).sum := by decide
  have hdescent : baseEnd_8139229 < baseStart_8139229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139270 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_8139270 : Nat := 118140960795 + 8139270 * 2 ^ 59
def prefixEnd_8139270 : Nat := 4983230072969 + 3 ^ 40 * 8139270 * 2
def baseEnd_8139270 : Nat := 4179357686720475302393185

theorem tailTrace_8139270 : CollatzResearch.WordTrace tailWord_8139270 prefixEnd_8139270 4179357686720475302393185 := by
  unfold tailWord_8139270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276986413213198171607977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197909043481881560994303509 9276986413213198171607977)
  ·
    refine ⟨6957739809909898628705983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9276986413213198171607977 6957739809909898628705983)
    ·
      refine ⟨10436609714864847943058975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6957739809909898628705983 10436609714864847943058975)
      ·
        refine ⟨15654914572297271914588463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10436609714864847943058975 15654914572297271914588463)
        ·
          refine ⟨23482371858445907871882695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15654914572297271914588463 23482371858445907871882695)
          ·
            refine ⟨35223557787668861807824043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23482371858445907871882695 35223557787668861807824043)
            ·
              refine ⟨52835336681503292711736065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35223557787668861807824043 52835336681503292711736065)
              ·
                refine ⟨39626502511127469533802049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52835336681503292711736065 39626502511127469533802049)
                ·
                  refine ⟨29719876883345602150351537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39626502511127469533802049 29719876883345602150351537)
                  ·
                    refine ⟨22289907662509201612763653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29719876883345602150351537 22289907662509201612763653)
                    ·
                      refine ⟨4179357686720475302393185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22289907662509201612763653 4179357686720475302393185)
                      ·
                        rfl

theorem cell23_8139270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_8139270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139270 prefixEnd_8139270 := by exact prefixLift 8139270
  have htrace : WordTrace (prefixWord ++ tailWord_8139270) baseStart_8139270 baseEnd_8139270 := by
    simpa [prefixWord, tailWord_8139270, baseEnd_8139270] using wordTrace_append hprefix tailTrace_8139270
  have hstable : (prefixWord ++ tailWord_8139270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139270).length < 2 ^ (prefixWord ++ tailWord_8139270).sum := by decide
  have hdescent : baseEnd_8139270 < baseStart_8139270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139289 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 7, 4]
def baseStart_8139289 : Nat := 118140960795 + 8139289 * 2 ^ 59
def prefixEnd_8139289 : Nat := 4983230072969 + 3 ^ 40 * 8139289 * 2
def baseEnd_8139289 : Nat := 1393122480950970242685199

theorem tailTrace_8139289 : CollatzResearch.WordTrace tailWord_8139289 prefixEnd_8139289 1393122480950970242685199 := by
  unfold tailWord_8139289
  simp only [CollatzResearch.WordTrace]
  refine ⟨296864258209753507736396921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197909505473169005157597947 296864258209753507736396921)
  ·
    refine ⟨222648193657315130802297691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296864258209753507736396921 222648193657315130802297691)
    ·
      refine ⟨333972290485972696203446537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222648193657315130802297691 333972290485972696203446537)
      ·
        refine ⟨250479217864479522152584903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333972290485972696203446537 250479217864479522152584903)
        ·
          refine ⟨375718826796719283228877355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250479217864479522152584903 375718826796719283228877355)
          ·
            refine ⟨563578240195078924843316033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375718826796719283228877355 563578240195078924843316033)
            ·
              refine ⟨422683680146309193632487025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563578240195078924843316033 422683680146309193632487025)
              ·
                refine ⟨317012760109731895224365269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422683680146309193632487025 317012760109731895224365269)
                ·
                  refine ⟨7429986565071841294321061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 317012760109731895224365269 7429986565071841294321061)
                  ·
                    refine ⟨1393122480950970242685199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429986565071841294321061 1393122480950970242685199)
                    ·
                      rfl

theorem cell23_8139289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_8139289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139289 prefixEnd_8139289 := by exact prefixLift 8139289
  have htrace : WordTrace (prefixWord ++ tailWord_8139289) baseStart_8139289 baseEnd_8139289 := by
    simpa [prefixWord, tailWord_8139289, baseEnd_8139289] using wordTrace_append hprefix tailTrace_8139289
  have hstable : (prefixWord ++ tailWord_8139289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139289).length < 2 ^ (prefixWord ++ tailWord_8139289).sum := by decide
  have hdescent : baseEnd_8139289 < baseStart_8139289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139340 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_8139340 : Nat := 118140960795 + 8139340 * 2 ^ 59
def prefixEnd_8139340 : Nat := 4983230072969 + 3 ^ 40 * 8139340 * 2
def baseEnd_8139340 : Nat := 1393131210122096676172621

theorem tailTrace_8139340 : CollatzResearch.WordTrace tailWord_8139340 prefixEnd_8139340 1393131210122096676172621 := by
  unfold tailWord_8139340
  simp only [CollatzResearch.WordTrace]
  refine ⟨148433059166284371723251737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197910745555045828964335649 148433059166284371723251737)
  ·
    refine ⟨111324794374713278792438803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148433059166284371723251737 111324794374713278792438803)
    ·
      refine ⟨166987191562069918188658205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111324794374713278792438803 166987191562069918188658205)
      ·
        refine ⟨62620196835776219320746827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166987191562069918188658205 62620196835776219320746827)
        ·
          refine ⟨93930295253664328981120241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62620196835776219320746827 93930295253664328981120241)
          ·
            refine ⟨70447721440248246735840181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93930295253664328981120241 70447721440248246735840181)
            ·
              refine ⟨6604473885023273131485017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70447721440248246735840181 6604473885023273131485017)
              ·
                refine ⟨4953355413767454848613763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604473885023273131485017 4953355413767454848613763)
                ·
                  refine ⟨7430033120651182272920645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953355413767454848613763 7430033120651182272920645)
                  ·
                    refine ⟨1393131210122096676172621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7430033120651182272920645 1393131210122096676172621)
                    ·
                      rfl

theorem cell23_8139340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_8139340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139340 prefixEnd_8139340 := by exact prefixLift 8139340
  have htrace : WordTrace (prefixWord ++ tailWord_8139340) baseStart_8139340 baseEnd_8139340 := by
    simpa [prefixWord, tailWord_8139340, baseEnd_8139340] using wordTrace_append hprefix tailTrace_8139340
  have hstable : (prefixWord ++ tailWord_8139340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139340).length < 2 ^ (prefixWord ++ tailWord_8139340).sum := by decide
  have hdescent : baseEnd_8139340 < baseStart_8139340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139386 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2]
def baseStart_8139386 : Nat := 118140960795 + 8139386 * 2 ^ 59
def prefixEnd_8139386 : Nat := 4983230072969 + 3 ^ 40 * 8139386 * 2
def baseEnd_8139386 : Nat := 4179417250476396848542651

theorem tailTrace_8139386 : CollatzResearch.WordTrace tailWord_8139386 prefixEnd_8139386 4179417250476396848542651 := by
  unfold tailWord_8139386
  simp only [CollatzResearch.WordTrace]
  refine ⟨74216949022600523325669503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197911864060268062201785341 74216949022600523325669503)
  ·
    refine ⟨111325423533900784988504255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74216949022600523325669503 111325423533900784988504255)
    ·
      refine ⟨166988135300851177482756383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111325423533900784988504255 166988135300851177482756383)
      ·
        refine ⟨250482202951276766224134575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166988135300851177482756383 250482202951276766224134575)
        ·
          refine ⟨375723304426915149336201863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250482202951276766224134575 375723304426915149336201863)
          ·
            refine ⟨563584956640372724004302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375723304426915149336201863 563584956640372724004302795)
            ·
              refine ⟨845377434960559086006454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563584956640372724004302795 845377434960559086006454193)
              ·
                refine ⟨634033076220419314504840645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845377434960559086006454193 634033076220419314504840645)
                ·
                  refine ⟨118881201791328621469657621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634033076220419314504840645 118881201791328621469657621)
                  ·
                    refine ⟨5572556333968529131390201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118881201791328621469657621 5572556333968529131390201)
                    ·
                      refine ⟨4179417250476396848542651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572556333968529131390201 4179417250476396848542651)
                      ·
                        rfl

theorem cell23_8139386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_8139386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139386 prefixEnd_8139386 := by exact prefixLift 8139386
  have htrace : WordTrace (prefixWord ++ tailWord_8139386) baseStart_8139386 baseEnd_8139386 := by
    simpa [prefixWord, tailWord_8139386, baseEnd_8139386] using wordTrace_append hprefix tailTrace_8139386
  have hstable : (prefixWord ++ tailWord_8139386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139386).length < 2 ^ (prefixWord ++ tailWord_8139386).sum := by decide
  have hdescent : baseEnd_8139386 < baseStart_8139386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139397 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 1, 1, 3]
def baseStart_8139397 : Nat := 118140960795 + 8139397 * 2 ^ 59
def prefixEnd_8139397 : Nat := 4983230072969 + 3 ^ 40 * 8139397 * 2
def baseEnd_8139397 : Nat := 4179422898763596305505101

theorem tailTrace_8139397 : CollatzResearch.WordTrace tailWord_8139397 prefixEnd_8139397 4179422898763596305505101 := by
  unfold tailWord_8139397
  simp only [CollatzResearch.WordTrace]
  refine ⟨296868197293362242181328445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197912131528908161454218963 296868197293362242181328445)
  ·
    refine ⟨111325573985010840817998167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296868197293362242181328445 111325573985010840817998167)
    ·
      refine ⟨166988360977516261226997251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111325573985010840817998167 166988360977516261226997251)
      ·
        refine ⟨250482541466274391840495877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166988360977516261226997251 250482541466274391840495877)
        ·
          refine ⟨46965476524926448470092977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250482541466274391840495877 46965476524926448470092977)
          ·
            refine ⟨35224107393694836352569733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46965476524926448470092977 35224107393694836352569733)
            ·
              refine ⟨6604520136317781816106825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35224107393694836352569733 6604520136317781816106825)
              ·
                refine ⟨4953390102238336362080119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604520136317781816106825 4953390102238336362080119)
                ·
                  refine ⟨7430085153357504543120179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953390102238336362080119 7430085153357504543120179)
                  ·
                    refine ⟨11145127730036256814680269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7430085153357504543120179 11145127730036256814680269)
                    ·
                      refine ⟨4179422898763596305505101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11145127730036256814680269 4179422898763596305505101)
                      ·
                        rfl

theorem cell23_8139397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_8139397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139397 prefixEnd_8139397 := by exact prefixLift 8139397
  have htrace : WordTrace (prefixWord ++ tailWord_8139397) baseStart_8139397 baseEnd_8139397 := by
    simpa [prefixWord, tailWord_8139397, baseEnd_8139397] using wordTrace_append hprefix tailTrace_8139397
  have hstable : (prefixWord ++ tailWord_8139397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139397).length < 2 ^ (prefixWord ++ tailWord_8139397).sum := by decide
  have hdescent : baseEnd_8139397 < baseStart_8139397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139406 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_8139406 : Nat := 118140960795 + 8139406 * 2 ^ 59
def prefixEnd_8139406 : Nat := 4983230072969 + 3 ^ 40 * 8139406 * 2
def baseEnd_8139406 : Nat := 4179427520089486770292559

theorem tailTrace_8139406 : CollatzResearch.WordTrace tailWord_8139406 prefixEnd_8139406 4179427520089486770292559 := by
  unfold tailWord_8139406
  simp only [CollatzResearch.WordTrace]
  refine ⟨37108565693791204589800759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197912350366886424478937381 37108565693791204589800759)
  ·
    refine ⟨55662848540686806884701139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37108565693791204589800759 55662848540686806884701139)
    ·
      refine ⟨83494272811030210327051709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55662848540686806884701139 83494272811030210327051709)
      ·
        refine ⟨31310352304136328872644391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83494272811030210327051709 31310352304136328872644391)
        ·
          refine ⟨46965528456204493308966587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31310352304136328872644391 46965528456204493308966587)
          ·
            refine ⟨70448292684306739963449881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46965528456204493308966587 70448292684306739963449881)
            ·
              refine ⟨52836219513230054972587411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70448292684306739963449881 52836219513230054972587411)
              ·
                refine ⟨79254329269845082458881117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52836219513230054972587411 79254329269845082458881117)
                ·
                  refine ⟨29720373476191905922080419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79254329269845082458881117 29720373476191905922080419)
                  ·
                    refine ⟨44580560214287858883120629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29720373476191905922080419 44580560214287858883120629)
                    ·
                      refine ⟨4179427520089486770292559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44580560214287858883120629 4179427520089486770292559)
                      ·
                        rfl

theorem cell23_8139406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_8139406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139406 prefixEnd_8139406 := by exact prefixLift 8139406
  have htrace : WordTrace (prefixWord ++ tailWord_8139406) baseStart_8139406 baseEnd_8139406 := by
    simpa [prefixWord, tailWord_8139406, baseEnd_8139406] using wordTrace_append hprefix tailTrace_8139406
  have hstable : (prefixWord ++ tailWord_8139406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139406).length < 2 ^ (prefixWord ++ tailWord_8139406).sum := by decide
  have hdescent : baseEnd_8139406 < baseStart_8139406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139420 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_8139420 : Nat := 118140960795 + 8139420 * 2 ^ 59
def prefixEnd_8139420 : Nat := 4983230072969 + 3 ^ 40 * 8139420 * 2
def baseEnd_8139420 : Nat := 4179434708818649715517495

theorem tailTrace_8139420 : CollatzResearch.WordTrace tailWord_8139420 prefixEnd_8139420 4179434708818649715517495 := by
  unfold tailWord_8139420
  simp only [CollatzResearch.WordTrace]
  refine ⟨148434518086139458554707857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197912690781519278072943809 148434518086139458554707857)
  ·
    refine ⟨111325888564604593916030893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148434518086139458554707857 111325888564604593916030893)
    ·
      refine ⟨41747208211726722718511585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111325888564604593916030893 41747208211726722718511585)
      ·
        refine ⟨31310406158795042038883689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41747208211726722718511585 31310406158795042038883689)
        ·
          refine ⟨23482804619096281529162767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31310406158795042038883689 23482804619096281529162767)
          ·
            refine ⟨35224206928644422293744151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23482804619096281529162767 35224206928644422293744151)
            ·
              refine ⟨52836310392966633440616227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35224206928644422293744151 52836310392966633440616227)
              ·
                refine ⟨79254465589449950160924341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52836310392966633440616227 79254465589449950160924341)
                ·
                  refine ⟨7430106149010932827586657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79254465589449950160924341 7430106149010932827586657)
                  ·
                    refine ⟨5572579611758199620689993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7430106149010932827586657 5572579611758199620689993)
                    ·
                      refine ⟨4179434708818649715517495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572579611758199620689993 4179434708818649715517495)
                      ·
                        rfl

theorem cell23_8139420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_8139420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139420 prefixEnd_8139420 := by exact prefixLift 8139420
  have htrace : WordTrace (prefixWord ++ tailWord_8139420) baseStart_8139420 baseEnd_8139420 := by
    simpa [prefixWord, tailWord_8139420, baseEnd_8139420] using wordTrace_append hprefix tailTrace_8139420
  have hstable : (prefixWord ++ tailWord_8139420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139420).length < 2 ^ (prefixWord ++ tailWord_8139420).sum := by decide
  have hdescent : baseEnd_8139420 < baseStart_8139420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139434 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_8139434 : Nat := 118140960795 + 8139434 * 2 ^ 59
def prefixEnd_8139434 : Nat := 4983230072969 + 3 ^ 40 * 8139434 * 2
def baseEnd_8139434 : Nat := 1393147299182604220247477

theorem tailTrace_8139434 : CollatzResearch.WordTrace tailWord_8139434 prefixEnd_8139434 1393147299182604220247477 := by
  unfold tailWord_8139434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74217386698557049375106339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197913031196152131666950237 74217386698557049375106339)
  ·
    refine ⟨111326080047835574062659509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74217386698557049375106339 111326080047835574062659509)
    ·
      refine ⟨10436820004484585068374329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111326080047835574062659509 10436820004484585068374329)
      ·
        refine ⟨7827615003363438801280747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10436820004484585068374329 7827615003363438801280747)
        ·
          refine ⟨11741422505045158201921121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827615003363438801280747 11741422505045158201921121)
          ·
            refine ⟨8806066878783868651440841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11741422505045158201921121 8806066878783868651440841)
            ·
              refine ⟨6604550159087901488580631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806066878783868651440841 6604550159087901488580631)
              ·
                refine ⟨9906825238631852232870947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6604550159087901488580631 9906825238631852232870947)
                ·
                  refine ⟨14860237857947778349306421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9906825238631852232870947 14860237857947778349306421)
                  ·
                    refine ⟨1393147299182604220247477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14860237857947778349306421 1393147299182604220247477)
                    ·
                      rfl

theorem cell23_8139434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_8139434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139434 prefixEnd_8139434 := by exact prefixLift 8139434
  have htrace : WordTrace (prefixWord ++ tailWord_8139434) baseStart_8139434 baseEnd_8139434 := by
    simpa [prefixWord, tailWord_8139434, baseEnd_8139434] using wordTrace_append hprefix tailTrace_8139434
  have hstable : (prefixWord ++ tailWord_8139434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139434).length < 2 ^ (prefixWord ++ tailWord_8139434).sum := by decide
  have hdescent : baseEnd_8139434 < baseStart_8139434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139437 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_8139437 : Nat := 118140960795 + 8139437 * 2 ^ 59
def prefixEnd_8139437 : Nat := 4983230072969 + 3 ^ 40 * 8139437 * 2
def baseEnd_8139437 : Nat := 4179443437989776149004917

theorem tailTrace_8139437 : CollatzResearch.WordTrace tailWord_8139437 prefixEnd_8139437 4179443437989776149004917 := by
  unfold tailWord_8139437
  simp only [CollatzResearch.WordTrace]
  refine ⟨296869656213217329012784565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197913104142144886008523043 296869656213217329012784565)
  ·
    refine ⟨27831530269989124594948553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296869656213217329012784565 27831530269989124594948553)
    ·
      refine ⟨20873647702491843446211415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27831530269989124594948553 20873647702491843446211415)
      ·
        refine ⟨31310471553737765169317123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20873647702491843446211415 31310471553737765169317123)
        ·
          refine ⟨46965707330606647753975685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31310471553737765169317123 46965707330606647753975685)
          ·
            refine ⟨8806070124488746453870441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46965707330606647753975685 8806070124488746453870441)
            ·
              refine ⟨6604552593366559840402831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806070124488746453870441 6604552593366559840402831)
              ·
                refine ⟨9906828890049839760604247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6604552593366559840402831 9906828890049839760604247)
                ·
                  refine ⟨14860243335074759640906371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9906828890049839760604247 14860243335074759640906371)
                  ·
                    refine ⟨22290365002612139461359557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14860243335074759640906371 22290365002612139461359557)
                    ·
                      refine ⟨4179443437989776149004917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22290365002612139461359557 4179443437989776149004917)
                      ·
                        rfl

theorem cell23_8139437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_8139437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139437 prefixEnd_8139437 := by exact prefixLift 8139437
  have htrace : WordTrace (prefixWord ++ tailWord_8139437) baseStart_8139437 baseEnd_8139437 := by
    simpa [prefixWord, tailWord_8139437, baseEnd_8139437] using wordTrace_append hprefix tailTrace_8139437
  have hstable : (prefixWord ++ tailWord_8139437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139437).length < 2 ^ (prefixWord ++ tailWord_8139437).sum := by decide
  have hdescent : baseEnd_8139437 < baseStart_8139437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139447 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 2, 4]
def baseStart_8139447 : Nat := 118140960795 + 8139447 * 2 ^ 59
def prefixEnd_8139447 : Nat := 4983230072969 + 3 ^ 40 * 8139447 * 2
def baseEnd_8139447 : Nat := 1393149524265440369959957

theorem tailTrace_8139447 : CollatzResearch.WordTrace tailWord_8139447 prefixEnd_8139447 1393149524265440369959957 := by
  unfold tailWord_8139447
  simp only [CollatzResearch.WordTrace]
  refine ⟨296870020943181100720648595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197913347295454067147099063 296870020943181100720648595)
  ·
    refine ⟨445305031414771651080972893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296870020943181100720648595 445305031414771651080972893)
    ·
      refine ⟨166989386780539369155364835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445305031414771651080972893 166989386780539369155364835)
      ·
        refine ⟨250484080170809053733047253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166989386780539369155364835 250484080170809053733047253)
        ·
          refine ⟨5870720629003337196868295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 250484080170809053733047253 5870720629003337196868295)
          ·
            refine ⟨8806080943505005795302443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870720629003337196868295 8806080943505005795302443)
            ·
              refine ⟨13209121415257508692953665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806080943505005795302443 13209121415257508692953665)
              ·
                refine ⟨9906841061443131519715249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13209121415257508692953665 9906841061443131519715249)
                ·
                  refine ⟨7430130796082348639786437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9906841061443131519715249 7430130796082348639786437)
                  ·
                    refine ⟨1393149524265440369959957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7430130796082348639786437 1393149524265440369959957)
                    ·
                      rfl

theorem cell23_8139447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_8139447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139447 prefixEnd_8139447 := by exact prefixLift 8139447
  have htrace : WordTrace (prefixWord ++ tailWord_8139447) baseStart_8139447 baseEnd_8139447 := by
    simpa [prefixWord, tailWord_8139447, baseEnd_8139447] using wordTrace_append hprefix tailTrace_8139447
  have hstable : (prefixWord ++ tailWord_8139447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139447).length < 2 ^ (prefixWord ++ tailWord_8139447).sum := by decide
  have hdescent : baseEnd_8139447 < baseStart_8139447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139463 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_8139463 : Nat := 118140960795 + 8139463 * 2 ^ 59
def prefixEnd_8139463 : Nat := 4983230072969 + 3 ^ 40 * 8139463 * 2
def baseEnd_8139463 : Nat := 4179456788486793047279797

theorem tailTrace_8139463 : CollatzResearch.WordTrace tailWord_8139463 prefixEnd_8139463 4179456788486793047279797 := by
  unfold tailWord_8139463
  simp only [CollatzResearch.WordTrace]
  refine ⟨296870604511123135453231043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197913736340748756968820695 296870604511123135453231043)
  ·
    refine ⟨445305906766684703179846565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296870604511123135453231043 445305906766684703179846565)
    ·
      refine ⟨83494857518753381846221231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445305906766684703179846565 83494857518753381846221231)
      ·
        refine ⟨125242286278130072769331847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83494857518753381846221231 125242286278130072769331847)
        ·
          refine ⟨187863429417195109153997771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125242286278130072769331847 187863429417195109153997771)
          ·
            refine ⟨281795144125792663730996657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187863429417195109153997771 281795144125792663730996657)
            ·
              refine ⟨211346358094344497798247493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281795144125792663730996657 211346358094344497798247493)
              ·
                refine ⟨39627442142689593337171405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211346358094344497798247493 39627442142689593337171405)
                ·
                  refine ⟨14860290803508597501439277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39627442142689593337171405 14860290803508597501439277)
                  ·
                    refine ⟨5572609051315724063039729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14860290803508597501439277 5572609051315724063039729)
                    ·
                      refine ⟨4179456788486793047279797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572609051315724063039729 4179456788486793047279797)
                      ·
                        rfl

theorem cell23_8139463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_8139463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139463 prefixEnd_8139463 := by exact prefixLift 8139463
  have htrace : WordTrace (prefixWord ++ tailWord_8139463) baseStart_8139463 baseEnd_8139463 := by
    simpa [prefixWord, tailWord_8139463, baseEnd_8139463] using wordTrace_append hprefix tailTrace_8139463
  have hstable : (prefixWord ++ tailWord_8139463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139463).length < 2 ^ (prefixWord ++ tailWord_8139463).sum := by decide
  have hdescent : baseEnd_8139463 < baseStart_8139463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139470 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_8139470 : Nat := 118140960795 + 8139470 * 2 ^ 59
def prefixEnd_8139470 : Nat := 4983230072969 + 3 ^ 40 * 8139470 * 2
def baseEnd_8139470 : Nat := 4179460382851374519892265

theorem tailTrace_8139470 : CollatzResearch.WordTrace tailWord_8139470 prefixEnd_8139470 4179460382851374519892265 := by
  unfold tailWord_8139470
  simp only [CollatzResearch.WordTrace]
  refine ⟨37108857477762221956091983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197913906548065183765823909 37108857477762221956091983)
  ·
    refine ⟨55663286216643332934137975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37108857477762221956091983 55663286216643332934137975)
    ·
      refine ⟨83494929324964999401206963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55663286216643332934137975 83494929324964999401206963)
      ·
        refine ⟨125242393987447499101810445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83494929324964999401206963 125242393987447499101810445)
        ·
          refine ⟨46965897745292812163178917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125242393987447499101810445 46965897745292812163178917)
          ·
            refine ⟨8806105827242402280596047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46965897745292812163178917 8806105827242402280596047)
            ·
              refine ⟨13209158740863603420894071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806105827242402280596047 13209158740863603420894071)
              ·
                refine ⟨19813738111295405131341107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13209158740863603420894071 19813738111295405131341107)
                ·
                  refine ⟨29720607166943107697011661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19813738111295405131341107 29720607166943107697011661)
                  ·
                    refine ⟨11145227687603665386379373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29720607166943107697011661 11145227687603665386379373)
                    ·
                      refine ⟨4179460382851374519892265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11145227687603665386379373 4179460382851374519892265)
                      ·
                        rfl

theorem cell23_8139470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_8139470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139470 prefixEnd_8139470 := by exact prefixLift 8139470
  have htrace : WordTrace (prefixWord ++ tailWord_8139470) baseStart_8139470 baseEnd_8139470 := by
    simpa [prefixWord, tailWord_8139470, baseEnd_8139470] using wordTrace_append hprefix tailTrace_8139470
  have hstable : (prefixWord ++ tailWord_8139470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139470).length < 2 ^ (prefixWord ++ tailWord_8139470).sum := by decide
  have hdescent : baseEnd_8139470 < baseStart_8139470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139477 : List Nat := [1, 3, 2, 5, 2, 1, 2, 7]
def baseStart_8139477 : Nat := 118140960795 + 8139477 * 2 ^ 59
def prefixEnd_8139477 : Nat := 4983230072969 + 3 ^ 40 * 8139477 * 2
def baseEnd_8139477 : Nat := 154794962119109481203879

theorem tailTrace_8139477 : CollatzResearch.WordTrace tailWord_8139477 prefixEnd_8139477 154794962119109481203879 := by
  unfold tailWord_8139477
  simp only [CollatzResearch.WordTrace]
  refine ⟨296871115133072415844240685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197914076755381610562827123 296871115133072415844240685)
  ·
    refine ⟨111326668174902155941590257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296871115133072415844240685 111326668174902155941590257)
    ·
      refine ⟨83495001131176616956192693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111326668174902155941590257 83495001131176616956192693)
      ·
        refine ⟨7827656356047807839643065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83495001131176616956192693 7827656356047807839643065)
        ·
          refine ⟨5870742267035855879732299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7827656356047807839643065 5870742267035855879732299)
          ·
            refine ⟨8806113400553783819598449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870742267035855879732299 8806113400553783819598449)
            ·
              refine ⟨6604585050415337864698837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806113400553783819598449 6604585050415337864698837)
              ·
                refine ⟨154794962119109481203879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6604585050415337864698837 154794962119109481203879)
                ·
                  rfl

theorem cell23_8139477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 7].length) (baseStart_8139477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139477 prefixEnd_8139477 := by exact prefixLift 8139477
  have htrace : WordTrace (prefixWord ++ tailWord_8139477) baseStart_8139477 baseEnd_8139477 := by
    simpa [prefixWord, tailWord_8139477, baseEnd_8139477] using wordTrace_append hprefix tailTrace_8139477
  have hstable : (prefixWord ++ tailWord_8139477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139477).length < 2 ^ (prefixWord ++ tailWord_8139477).sum := by decide
  have hdescent : baseEnd_8139477 < baseStart_8139477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139480 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 1, 3, 2]
def baseStart_8139480 : Nat := 118140960795 + 8139480 * 2 ^ 59
def prefixEnd_8139480 : Nat := 4983230072969 + 3 ^ 40 * 8139480 * 2
def baseEnd_8139480 : Nat := 4179465517657919480767219

theorem tailTrace_8139480 : CollatzResearch.WordTrace tailWord_8139480 prefixEnd_8139480 4179465517657919480767219 := by
  unfold tailWord_8139480
  simp only [CollatzResearch.WordTrace]
  refine ⟨148435612276030773678299947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197914149701374364904399929 148435612276030773678299947)
  ·
    refine ⟨222653418414046160517449921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148435612276030773678299947 222653418414046160517449921)
    ·
      refine ⟨166990063810534620388087441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222653418414046160517449921 166990063810534620388087441)
      ·
        refine ⟨125242547857900965291065581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166990063810534620388087441 125242547857900965291065581)
        ·
          refine ⟨46965955446712861984149593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125242547857900965291065581 46965955446712861984149593)
          ·
            refine ⟨35224466585034646488112195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46965955446712861984149593 35224466585034646488112195)
            ·
              refine ⟨52836699877551969732168293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35224466585034646488112195 52836699877551969732168293)
              ·
                refine ⟨9906881227040994324781555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52836699877551969732168293 9906881227040994324781555)
                ·
                  refine ⟨14860321840561491487172333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9906881227040994324781555 14860321840561491487172333)
                  ·
                    refine ⟨5572620690210559307689625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14860321840561491487172333 5572620690210559307689625)
                    ·
                      refine ⟨4179465517657919480767219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572620690210559307689625 4179465517657919480767219)
                      ·
                        rfl

theorem cell23_8139480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_8139480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139480 prefixEnd_8139480 := by exact prefixLift 8139480
  have htrace : WordTrace (prefixWord ++ tailWord_8139480) baseStart_8139480 baseEnd_8139480 := by
    simpa [prefixWord, tailWord_8139480, baseEnd_8139480] using wordTrace_append hprefix tailTrace_8139480
  have hstable : (prefixWord ++ tailWord_8139480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139480).length < 2 ^ (prefixWord ++ tailWord_8139480).sum := by decide
  have hdescent : baseEnd_8139480 < baseStart_8139480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139573 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_8139573 : Nat := 118140960795 + 8139573 * 2 ^ 59
def prefixEnd_8139573 : Nat := 4983230072969 + 3 ^ 40 * 8139573 * 2
def baseEnd_8139573 : Nat := 4179513271358787616904291

theorem tailTrace_8139573 : CollatzResearch.WordTrace tailWord_8139573 prefixEnd_8139573 4179513271358787616904291 := by
  unfold tailWord_8139573
  simp only [CollatzResearch.WordTrace]
  refine ⟨296874616540724624239735373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197916411027149749493156915 296874616540724624239735373)
  ·
    refine ⟨111327981202771734089900765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296874616540724624239735373 111327981202771734089900765)
    ·
      refine ⟨41747992951039400283712787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111327981202771734089900765 41747992951039400283712787)
      ·
        refine ⟨62621989426559100425569181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41747992951039400283712787 62621989426559100425569181)
        ·
          refine ⟨23483246034959662659588443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62621989426559100425569181 23483246034959662659588443)
          ·
            refine ⟨35224869052439493989382665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23483246034959662659588443 35224869052439493989382665)
            ·
              refine ⟨26418651789329620492036999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35224869052439493989382665 26418651789329620492036999)
              ·
                refine ⟨39627977683994430738055499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26418651789329620492036999 39627977683994430738055499)
                ·
                  refine ⟨59441966525991646107083249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39627977683994430738055499 59441966525991646107083249)
                  ·
                    refine ⟨44581474894493734580312437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59441966525991646107083249 44581474894493734580312437)
                    ·
                      refine ⟨4179513271358787616904291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44581474894493734580312437 4179513271358787616904291)
                      ·
                        rfl

theorem cell23_8139573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_8139573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139573 prefixEnd_8139573 := by exact prefixLift 8139573
  have htrace : WordTrace (prefixWord ++ tailWord_8139573) baseStart_8139573 baseEnd_8139573 := by
    simpa [prefixWord, tailWord_8139573, baseEnd_8139573] using wordTrace_append hprefix tailTrace_8139573
  have hstable : (prefixWord ++ tailWord_8139573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139573).length < 2 ^ (prefixWord ++ tailWord_8139573).sum := by decide
  have hdescent : baseEnd_8139573 < baseStart_8139573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139593 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 5, 4]
def baseStart_8139593 : Nat := 118140960795 + 8139593 * 2 ^ 59
def prefixEnd_8139593 : Nat := 4983230072969 + 3 ^ 40 * 8139593 * 2
def baseEnd_8139593 : Nat := 1393174513657292512884733

theorem tailTrace_8139593 : CollatzResearch.WordTrace tailWord_8139593 prefixEnd_8139593 1393174513657292512884733 := by
  unfold tailWord_8139593
  simp only [CollatzResearch.WordTrace]
  refine ⟨296875346000652167655463433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197916897333768111770308955 296875346000652167655463433)
  ·
    refine ⟨222656509500489125741597575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296875346000652167655463433 222656509500489125741597575)
    ·
      refine ⟨333984764250733688612396363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222656509500489125741597575 333984764250733688612396363)
      ·
        refine ⟨500977146376100532918594545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333984764250733688612396363 500977146376100532918594545)
        ·
          refine ⟨375732859782075399688945909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500977146376100532918594545 375732859782075399688945909)
          ·
            refine ⟨35224955604569568720838679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375732859782075399688945909 35224955604569568720838679)
            ·
              refine ⟨52837433406854353081258019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35224955604569568720838679 52837433406854353081258019)
              ·
                refine ⟨79256150110281529621887029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52837433406854353081258019 79256150110281529621887029)
                ·
                  refine ⟨7430264072838893402051909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79256150110281529621887029 7430264072838893402051909)
                  ·
                    refine ⟨1393174513657292512884733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7430264072838893402051909 1393174513657292512884733)
                    ·
                      rfl

theorem cell23_8139593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_8139593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139593 prefixEnd_8139593 := by exact prefixLift 8139593
  have htrace : WordTrace (prefixWord ++ tailWord_8139593) baseStart_8139593 baseEnd_8139593 := by
    simpa [prefixWord, tailWord_8139593, baseEnd_8139593] using wordTrace_append hprefix tailTrace_8139593
  have hstable : (prefixWord ++ tailWord_8139593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139593).length < 2 ^ (prefixWord ++ tailWord_8139593).sum := by decide
  have hdescent : baseEnd_8139593 < baseStart_8139593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139623 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 8]
def baseStart_8139623 : Nat := 118140960795 + 8139623 * 2 ^ 59
def prefixEnd_8139623 : Nat := 4983230072969 + 3 ^ 40 * 8139623 * 2
def baseEnd_8139623 : Nat := 464393216154612491253229

theorem tailTrace_8139623 : CollatzResearch.WordTrace tailWord_8139623 prefixEnd_8139623 464393216154612491253229 := by
  unfold tailWord_8139623
  simp only [CollatzResearch.WordTrace]
  refine ⟨296876440190543482779055523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197917626793695655186037015 296876440190543482779055523)
  ·
    refine ⟨445314660285815224168583285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296876440190543482779055523 445314660285815224168583285)
    ·
      refine ⟨41748249401795177265804683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 445314660285815224168583285 41748249401795177265804683)
      ·
        refine ⟨62622374102692765898707025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41748249401795177265804683 62622374102692765898707025)
        ·
          refine ⟨46966780577019574424030269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62622374102692765898707025 46966780577019574424030269)
          ·
            refine ⟨17612542716382340409011351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46966780577019574424030269 17612542716382340409011351)
            ·
              refine ⟨26418814074573510613517027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17612542716382340409011351 26418814074573510613517027)
              ·
                refine ⟨39628221111860265920275541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26418814074573510613517027 39628221111860265920275541)
                ·
                  refine ⟨464393216154612491253229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39628221111860265920275541 464393216154612491253229)
                  ·
                    rfl

theorem cell23_8139623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 8].length) (baseStart_8139623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139623 prefixEnd_8139623 := by exact prefixLift 8139623
  have htrace : WordTrace (prefixWord ++ tailWord_8139623) baseStart_8139623 baseEnd_8139623 := by
    simpa [prefixWord, tailWord_8139623, baseEnd_8139623] using wordTrace_append hprefix tailTrace_8139623
  have hstable : (prefixWord ++ tailWord_8139623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139623).length < 2 ^ (prefixWord ++ tailWord_8139623).sum := by decide
  have hdescent : baseEnd_8139623 < baseStart_8139623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139660 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 1, 5, 2]
def baseStart_8139660 : Nat := 118140960795 + 8139660 * 2 ^ 59
def prefixEnd_8139660 : Nat := 4983230072969 + 3 ^ 40 * 8139660 * 2
def baseEnd_8139660 : Nat := 4179557944175728776516391

theorem tailTrace_8139660 : CollatzResearch.WordTrace tailWord_8139660 prefixEnd_8139660 4179557944175728776516391 := by
  unfold tailWord_8139660
  simp only [CollatzResearch.WordTrace]
  refine ⟨148438894845704719049076217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197918526460939625398768289 148438894845704719049076217)
  ·
    refine ⟨111329171134278539286807163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148438894845704719049076217 111329171134278539286807163)
    ·
      refine ⟨166993756701417808930210745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111329171134278539286807163 166993756701417808930210745)
      ·
        refine ⟨125245317526063356697658059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166993756701417808930210745 125245317526063356697658059)
        ·
          refine ⟨187867976289095035046487089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125245317526063356697658059 187867976289095035046487089)
          ·
            refine ⟨140900982216821276284865317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187867976289095035046487089 140900982216821276284865317)
            ·
              refine ⟨26418934165653989303412247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140900982216821276284865317 26418934165653989303412247)
              ·
                refine ⟨39628401248480983955118371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26418934165653989303412247 39628401248480983955118371)
                ·
                  refine ⟨59442601872721475932677557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39628401248480983955118371 59442601872721475932677557)
                  ·
                    refine ⟨5572743925567638368688521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59442601872721475932677557 5572743925567638368688521)
                    ·
                      refine ⟨4179557944175728776516391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572743925567638368688521 4179557944175728776516391)
                      ·
                        rfl

theorem cell23_8139660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_8139660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139660 prefixEnd_8139660 := by exact prefixLift 8139660
  have htrace : WordTrace (prefixWord ++ tailWord_8139660) baseStart_8139660 baseEnd_8139660 := by
    simpa [prefixWord, tailWord_8139660, baseEnd_8139660] using wordTrace_append hprefix tailTrace_8139660
  have hstable : (prefixWord ++ tailWord_8139660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139660).length < 2 ^ (prefixWord ++ tailWord_8139660).sum := by decide
  have hdescent : baseEnd_8139660 < baseStart_8139660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139667 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 1, 1, 3]
def baseStart_8139667 : Nat := 118140960795 + 8139667 * 2 ^ 59
def prefixEnd_8139667 : Nat := 4983230072969 + 3 ^ 40 * 8139667 * 2
def baseEnd_8139667 : Nat := 4179561538540310249128859

theorem tailTrace_8139667 : CollatzResearch.WordTrace tailWord_8139667 prefixEnd_8139667 4179561538540310249128859 := by
  unfold tailWord_8139667
  simp only [CollatzResearch.WordTrace]
  refine ⟨296878045002384078293657255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197918696668256052195771503 296878045002384078293657255)
  ·
    refine ⟨445317067503576117440485883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296878045002384078293657255 445317067503576117440485883)
    ·
      refine ⟨667975601255364176160728825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445317067503576117440485883 667975601255364176160728825)
      ·
        refine ⟨500981700941523132120546619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667975601255364176160728825 500981700941523132120546619)
        ·
          refine ⟨751472551412284698180819929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500981700941523132120546619 751472551412284698180819929)
          ·
            refine ⟨563604413559213523635614947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751472551412284698180819929 563604413559213523635614947)
            ·
              refine ⟨845406620338820285453422421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563604413559213523635614947 845406620338820285453422421)
              ·
                refine ⟨4953554416047775110078647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 845406620338820285453422421 4953554416047775110078647)
                ·
                  refine ⟨7430331624071662665117971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953554416047775110078647 7430331624071662665117971)
                  ·
                    refine ⟨11145497436107493997676957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7430331624071662665117971 11145497436107493997676957)
                    ·
                      refine ⟨4179561538540310249128859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11145497436107493997676957 4179561538540310249128859)
                      ·
                        rfl

theorem cell23_8139667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 1, 3].length) (baseStart_8139667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139667 prefixEnd_8139667 := by exact prefixLift 8139667
  have htrace : WordTrace (prefixWord ++ tailWord_8139667) baseStart_8139667 baseEnd_8139667 := by
    simpa [prefixWord, tailWord_8139667, baseEnd_8139667] using wordTrace_append hprefix tailTrace_8139667
  have hstable : (prefixWord ++ tailWord_8139667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139667).length < 2 ^ (prefixWord ++ tailWord_8139667).sum := by decide
  have hdescent : baseEnd_8139667 < baseStart_8139667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139673 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_8139673 : Nat := 118140960795 + 8139673 * 2 ^ 59
def prefixEnd_8139673 : Nat := 4983230072969 + 3 ^ 40 * 8139673 * 2
def baseEnd_8139673 : Nat := 4179564619424237225653831

theorem tailTrace_8139673 : CollatzResearch.WordTrace tailWord_8139673 prefixEnd_8139673 4179564619424237225653831 := by
  unfold tailWord_8139673
  simp only [CollatzResearch.WordTrace]
  refine ⟨296878263840362341318375673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197918842560241560878917115 296878263840362341318375673)
  ·
    refine ⟨222658697880271755988781755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296878263840362341318375673 222658697880271755988781755)
    ·
      refine ⟨333988046820407633983172633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222658697880271755988781755 333988046820407633983172633)
      ·
        refine ⟨250491035115305725487379475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333988046820407633983172633 250491035115305725487379475)
        ·
          refine ⟨375736552672958588231069213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250491035115305725487379475 375736552672958588231069213)
          ·
            refine ⟨140901207252359470586650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375736552672958588231069213 140901207252359470586650955)
            ·
              refine ⟨211351810878539205879976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140901207252359470586650955 211351810878539205879976433)
              ·
                refine ⟨158513858158904404409982325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211351810878539205879976433 158513858158904404409982325)
                ·
                  refine ⟨14860674202397287913435843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158513858158904404409982325 14860674202397287913435843)
                  ·
                    refine ⟨22291011303595931870153765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14860674202397287913435843 22291011303595931870153765)
                    ·
                      refine ⟨4179564619424237225653831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22291011303595931870153765 4179564619424237225653831)
                      ·
                        rfl

theorem cell23_8139673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_8139673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139673 prefixEnd_8139673 := by exact prefixLift 8139673
  have htrace : WordTrace (prefixWord ++ tailWord_8139673) baseStart_8139673 baseEnd_8139673 := by
    simpa [prefixWord, tailWord_8139673, baseEnd_8139673] using wordTrace_append hprefix tailTrace_8139673
  have hstable : (prefixWord ++ tailWord_8139673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139673).length < 2 ^ (prefixWord ++ tailWord_8139673).sum := by decide
  have hdescent : baseEnd_8139673 < baseStart_8139673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139677 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_8139677 : Nat := 118140960795 + 8139677 * 2 ^ 59
def prefixEnd_8139677 : Nat := 4983230072969 + 3 ^ 40 * 8139677 * 2
def baseEnd_8139677 : Nat := 4179566673346855210003813

theorem tailTrace_8139677 : CollatzResearch.WordTrace tailWord_8139677 prefixEnd_8139677 4179566673346855210003813 := by
  unfold tailWord_8139677
  simp only [CollatzResearch.WordTrace]
  refine ⟨296878409732347850001521285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197918939821565233334347523 296878409732347850001521285)
  ·
    refine ⟨55664701824815221875285241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296878409732347850001521285 55664701824815221875285241)
    ·
      refine ⟨41748526368611416406463931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55664701824815221875285241 41748526368611416406463931)
      ·
        refine ⟨62622789552917124609695897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41748526368611416406463931 62622789552917124609695897)
        ·
          refine ⟨46967092164687843457271923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62622789552917124609695897 46967092164687843457271923)
          ·
            refine ⟨70450638247031765185907885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46967092164687843457271923 70450638247031765185907885)
            ·
              refine ⟨26418989342636911944715457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70450638247031765185907885 26418989342636911944715457)
              ·
                refine ⟨19814242006977683958536593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26418989342636911944715457 19814242006977683958536593)
                ·
                  refine ⟨14860681505233262968902445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19814242006977683958536593 14860681505233262968902445)
                  ·
                    refine ⟨5572755564462473613338417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14860681505233262968902445 5572755564462473613338417)
                    ·
                      refine ⟨4179566673346855210003813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572755564462473613338417 4179566673346855210003813)
                      ·
                        rfl

theorem cell23_8139677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_8139677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139677 prefixEnd_8139677 := by exact prefixLift 8139677
  have htrace : WordTrace (prefixWord ++ tailWord_8139677) baseStart_8139677 baseEnd_8139677 := by
    simpa [prefixWord, tailWord_8139677, baseEnd_8139677] using wordTrace_append hprefix tailTrace_8139677
  have hstable : (prefixWord ++ tailWord_8139677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139677).length < 2 ^ (prefixWord ++ tailWord_8139677).sum := by decide
  have hdescent : baseEnd_8139677 < baseStart_8139677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139703 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_8139703 : Nat := 118140960795 + 8139703 * 2 ^ 59
def prefixEnd_8139703 : Nat := 4983230072969 + 3 ^ 40 * 8139703 * 2
def baseEnd_8139703 : Nat := 4179580023843872108278693

theorem tailTrace_8139703 : CollatzResearch.WordTrace tailWord_8139703 prefixEnd_8139703 4179580023843872108278693 := by
  unfold tailWord_8139703
  simp only [CollatzResearch.WordTrace]
  refine ⟨296879358030253656441967763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197919572020169104294645175 296879358030253656441967763)
  ·
    refine ⟨445319037045380484662951645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296879358030253656441967763 445319037045380484662951645)
    ·
      refine ⟨166994638892017681748606867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445319037045380484662951645 166994638892017681748606867)
      ·
        refine ⟨250491958338026522622910301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166994638892017681748606867 250491958338026522622910301)
        ·
          refine ⟨93934484376759945983591363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250491958338026522622910301 93934484376759945983591363)
          ·
            refine ⟨140901726565139918975387045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93934484376759945983591363 140901726565139918975387045)
            ·
              refine ⟨26419073730963734807885071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140901726565139918975387045 26419073730963734807885071)
              ·
                refine ⟨39628610596445602211827607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26419073730963734807885071 39628610596445602211827607)
                ·
                  refine ⟨59442915894668403317741411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39628610596445602211827607 59442915894668403317741411)
                  ·
                    refine ⟨89164373842002604976612117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59442915894668403317741411 89164373842002604976612117)
                    ·
                      refine ⟨4179580023843872108278693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89164373842002604976612117 4179580023843872108278693)
                      ·
                        rfl

theorem cell23_8139703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_8139703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139703 prefixEnd_8139703 := by exact prefixLift 8139703
  have htrace : WordTrace (prefixWord ++ tailWord_8139703) baseStart_8139703 baseEnd_8139703 := by
    simpa [prefixWord, tailWord_8139703, baseEnd_8139703] using wordTrace_append hprefix tailTrace_8139703
  have hstable : (prefixWord ++ tailWord_8139703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139703).length < 2 ^ (prefixWord ++ tailWord_8139703).sum := by decide
  have hdescent : baseEnd_8139703 < baseStart_8139703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139734 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_8139734 : Nat := 118140960795 + 8139734 * 2 ^ 59
def prefixEnd_8139734 : Nat := 4983230072969 + 3 ^ 40 * 8139734 * 2
def baseEnd_8139734 : Nat := 1393198647248053828997017

theorem tailTrace_8139734 : CollatzResearch.WordTrace tailWord_8139734 prefixEnd_8139734 1393198647248053828997017 := by
  unfold tailWord_8139734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18555030543321334296021641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197920325795427565824230837 18555030543321334296021641)
  ·
    refine ⟨13916272907491000722016231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18555030543321334296021641 13916272907491000722016231)
    ·
      refine ⟨20874409361236501083024347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13916272907491000722016231 20874409361236501083024347)
      ·
        refine ⟨31311614041854751624536521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20874409361236501083024347 31311614041854751624536521)
        ·
          refine ⟨23483710531391063718402391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31311614041854751624536521 23483710531391063718402391)
          ·
            refine ⟨35225565797086595577603587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23483710531391063718402391 35225565797086595577603587)
            ·
              refine ⟨52838348695629893366405381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35225565797086595577603587 52838348695629893366405381)
              ·
                refine ⟨9907190380430605006201009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52838348695629893366405381 9907190380430605006201009)
                ·
                  refine ⟨7430392785322953754650757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9907190380430605006201009 7430392785322953754650757)
                  ·
                    refine ⟨1393198647248053828997017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7430392785322953754650757 1393198647248053828997017)
                    ·
                      rfl

theorem cell23_8139734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_8139734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139734 prefixEnd_8139734 := by exact prefixLift 8139734
  have htrace : WordTrace (prefixWord ++ tailWord_8139734) baseStart_8139734 baseEnd_8139734 := by
    simpa [prefixWord, tailWord_8139734, baseEnd_8139734] using wordTrace_append hprefix tailTrace_8139734
  have hstable : (prefixWord ++ tailWord_8139734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139734).length < 2 ^ (prefixWord ++ tailWord_8139734).sum := by decide
  have hdescent : baseEnd_8139734 < baseStart_8139734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139773 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_8139773 : Nat := 118140960795 + 8139773 * 2 ^ 59
def prefixEnd_8139773 : Nat := 4983230072969 + 3 ^ 40 * 8139773 * 2
def baseEnd_8139773 : Nat := 1393205322496562278134457

theorem tailTrace_8139773 : CollatzResearch.WordTrace tailWord_8139773 prefixEnd_8139773 1393205322496562278134457 := by
  unfold tailWord_8139773
  simp only [CollatzResearch.WordTrace]
  refine ⟨296881911140000058397015973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197921274093333372264677315 296881911140000058397015973)
  ·
    refine ⟨55665358338750010949440495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296881911140000058397015973 55665358338750010949440495)
    ·
      refine ⟨83498037508125016424160743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55665358338750010949440495 83498037508125016424160743)
      ·
        refine ⟨125247056262187524636241115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83498037508125016424160743 125247056262187524636241115)
        ·
          refine ⟨187870584393281286954361673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125247056262187524636241115 187870584393281286954361673)
          ·
            refine ⟨140902938294960965215771255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187870584393281286954361673 140902938294960965215771255)
            ·
              refine ⟨211354407442441447823656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140902938294960965215771255 211354407442441447823656883)
              ·
                refine ⟨317031611163662171735485325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211354407442441447823656883 317031611163662171735485325)
                ·
                  refine ⟨118886854186373314400806997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317031611163662171735485325 118886854186373314400806997)
                  ·
                    refine ⟨1393205322496562278134457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118886854186373314400806997 1393205322496562278134457)
                    ·
                      rfl

theorem cell23_8139773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_8139773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139773 prefixEnd_8139773 := by exact prefixLift 8139773
  have htrace : WordTrace (prefixWord ++ tailWord_8139773) baseStart_8139773 baseEnd_8139773 := by
    simpa [prefixWord, tailWord_8139773, baseEnd_8139773] using wordTrace_append hprefix tailTrace_8139773
  have hstable : (prefixWord ++ tailWord_8139773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139773).length < 2 ^ (prefixWord ++ tailWord_8139773).sum := by decide
  have hdescent : baseEnd_8139773 < baseStart_8139773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139784 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_8139784 : Nat := 118140960795 + 8139784 * 2 ^ 59
def prefixEnd_8139784 : Nat := 4983230072969 + 3 ^ 40 * 8139784 * 2
def baseEnd_8139784 : Nat := 4179621615776886291365821

theorem tailTrace_8139784 : CollatzResearch.WordTrace tailWord_8139784 prefixEnd_8139784 4179621615776886291365821 := by
  unfold tailWord_8139784
  simp only [CollatzResearch.WordTrace]
  refine ⟨148441156171480103637833203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197921541561973471517110937 148441156171480103637833203)
  ·
    refine ⟨222661734257220155456749805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148441156171480103637833203 222661734257220155456749805)
    ·
      refine ⟨83498150346457558296281177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222661734257220155456749805 83498150346457558296281177)
      ·
        refine ⟨62623612759843168722210883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83498150346457558296281177 62623612759843168722210883)
        ·
          refine ⟨93935419139764753083316325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62623612759843168722210883 93935419139764753083316325)
          ·
            refine ⟨17612891088705891203121811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93935419139764753083316325 17612891088705891203121811)
            ·
              refine ⟨26419336633058836804682717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17612891088705891203121811 26419336633058836804682717)
              ·
                refine ⟨9907251237397063801756019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26419336633058836804682717 9907251237397063801756019)
                ·
                  refine ⟨14860876856095595702634029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9907251237397063801756019 14860876856095595702634029)
                  ·
                    refine ⟨5572828821035848388487761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14860876856095595702634029 5572828821035848388487761)
                    ·
                      refine ⟨4179621615776886291365821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5572828821035848388487761 4179621615776886291365821)
                      ·
                        rfl

theorem cell23_8139784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_8139784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139784 prefixEnd_8139784 := by exact prefixLift 8139784
  have htrace : WordTrace (prefixWord ++ tailWord_8139784) baseStart_8139784 baseEnd_8139784 := by
    simpa [prefixWord, tailWord_8139784, baseEnd_8139784] using wordTrace_append hprefix tailTrace_8139784
  have hstable : (prefixWord ++ tailWord_8139784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139784).length < 2 ^ (prefixWord ++ tailWord_8139784).sum := by decide
  have hdescent : baseEnd_8139784 < baseStart_8139784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139790 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_8139790 : Nat := 118140960795 + 8139790 * 2 ^ 59
def prefixEnd_8139790 : Nat := 4983230072969 + 3 ^ 40 * 8139790 * 2
def baseEnd_8139790 : Nat := 1393208232220271089296931

theorem tailTrace_8139790 : CollatzResearch.WordTrace tailWord_8139790 prefixEnd_8139790 1393208232220271089296931 := by
  unfold tailWord_8139790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110316397617308787548103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197921687453958980200256549 37110316397617308787548103)
  ·
    refine ⟨55665474596425963181322155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37110316397617308787548103 55665474596425963181322155)
    ·
      refine ⟨83498211894638944771983233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55665474596425963181322155 83498211894638944771983233)
      ·
        refine ⟨62623658920979208578987425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83498211894638944771983233 62623658920979208578987425)
        ·
          refine ⟨46967744190734406434240569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62623658920979208578987425 46967744190734406434240569)
          ·
            refine ⟨35225808143050804825680427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46967744190734406434240569 35225808143050804825680427)
            ·
              refine ⟨52838712214576207238520641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35225808143050804825680427 52838712214576207238520641)
              ·
                refine ⟨39629034160932155428890481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52838712214576207238520641 39629034160932155428890481)
                ·
                  refine ⟨29721775620699116571667861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39629034160932155428890481 29721775620699116571667861)
                  ·
                    refine ⟨1393208232220271089296931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29721775620699116571667861 1393208232220271089296931)
                    ·
                      rfl

theorem cell23_8139790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_8139790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139790 prefixEnd_8139790 := by exact prefixLift 8139790
  have htrace : WordTrace (prefixWord ++ tailWord_8139790) baseStart_8139790 baseEnd_8139790 := by
    simpa [prefixWord, tailWord_8139790, baseEnd_8139790] using wordTrace_append hprefix tailTrace_8139790
  have hstable : (prefixWord ++ tailWord_8139790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139790).length < 2 ^ (prefixWord ++ tailWord_8139790).sum := by decide
  have hdescent : baseEnd_8139790 < baseStart_8139790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139808 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8139808 : Nat := 118140960795 + 8139808 * 2 ^ 59
def prefixEnd_8139808 : Nat := 4983230072969 + 3 ^ 40 * 8139808 * 2
def baseEnd_8139808 : Nat := 4179633939312594197465711

theorem tailTrace_8139808 : CollatzResearch.WordTrace tailWord_8139808 prefixEnd_8139808 4179633939312594197465711 := by
  unfold tailWord_8139808
  simp only [CollatzResearch.WordTrace]
  refine ⟨148441593847436629687270039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197922125129915506249693385 148441593847436629687270039)
  ·
    refine ⟨222662390771154944530905059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148441593847436629687270039 222662390771154944530905059)
    ·
      refine ⟨333993586156732416796357589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222662390771154944530905059 333993586156732416796357589)
      ·
        refine ⟨7827974675548416018664631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 333993586156732416796357589 7827974675548416018664631)
        ·
          refine ⟨11741962013322624027996947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827974675548416018664631 11741962013322624027996947)
          ·
            refine ⟨17612943019983936041995421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11741962013322624027996947 17612943019983936041995421)
            ·
              refine ⟨6604853632493976015748283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17612943019983936041995421 6604853632493976015748283)
              ·
                refine ⟨9907280448740964023622425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6604853632493976015748283 9907280448740964023622425)
                ·
                  refine ⟨7430460336555723017716819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9907280448740964023622425 7430460336555723017716819)
                  ·
                    refine ⟨11145690504833584526575229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7430460336555723017716819 11145690504833584526575229)
                    ·
                      refine ⟨4179633939312594197465711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11145690504833584526575229 4179633939312594197465711)
                      ·
                        rfl

theorem cell23_8139808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8139808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139808 prefixEnd_8139808 := by exact prefixLift 8139808
  have htrace : WordTrace (prefixWord ++ tailWord_8139808) baseStart_8139808 baseEnd_8139808 := by
    simpa [prefixWord, tailWord_8139808, baseEnd_8139808] using wordTrace_append hprefix tailTrace_8139808
  have hstable : (prefixWord ++ tailWord_8139808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139808).length < 2 ^ (prefixWord ++ tailWord_8139808).sum := by decide
  have hdescent : baseEnd_8139808 < baseStart_8139808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139823 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_8139823 : Nat := 118140960795 + 8139823 * 2 ^ 59
def prefixEnd_8139823 : Nat := 4983230072969 + 3 ^ 40 * 8139823 * 2
def baseEnd_8139823 : Nat := 4179641641522411638778141

theorem tailTrace_8139823 : CollatzResearch.WordTrace tailWord_8139823 prefixEnd_8139823 4179641641522411638778141 := by
  unfold tailWord_8139823
  simp only [CollatzResearch.WordTrace]
  refine ⟨296883734789818916936336123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197922489859879277957557415 296883734789818916936336123)
  ·
    refine ⟨445325602184728375404504185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296883734789818916936336123 445325602184728375404504185)
    ·
      refine ⟨333994201638546281553378139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445325602184728375404504185 333994201638546281553378139)
      ·
        refine ⟨500991302457819422330067209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333994201638546281553378139 500991302457819422330067209)
        ·
          refine ⟨375743476843364566747550407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500991302457819422330067209 375743476843364566747550407)
          ·
            refine ⟨563615215265046850121325611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375743476843364566747550407 563615215265046850121325611)
            ·
              refine ⟨845422822897570275181988417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563615215265046850121325611 845422822897570275181988417)
              ·
                refine ⟨634067117173177706386491313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845422822897570275181988417 634067117173177706386491313)
                ·
                  refine ⟨475550337879883279789868485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634067117173177706386491313 475550337879883279789868485)
                  ·
                    refine ⟨89165688352478114960600341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475550337879883279789868485 89165688352478114960600341)
                    ·
                      refine ⟨4179641641522411638778141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89165688352478114960600341 4179641641522411638778141)
                      ·
                        rfl

theorem cell23_8139823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_8139823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139823 prefixEnd_8139823 := by exact prefixLift 8139823
  have htrace : WordTrace (prefixWord ++ tailWord_8139823) baseStart_8139823 baseEnd_8139823 := by
    simpa [prefixWord, tailWord_8139823, baseEnd_8139823] using wordTrace_append hprefix tailTrace_8139823
  have hstable : (prefixWord ++ tailWord_8139823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139823).length < 2 ^ (prefixWord ++ tailWord_8139823).sum := by decide
  have hdescent : baseEnd_8139823 < baseStart_8139823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139850 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_8139850 : Nat := 118140960795 + 8139850 * 2 ^ 59
def prefixEnd_8139850 : Nat := 4983230072969 + 3 ^ 40 * 8139850 * 2
def baseEnd_8139850 : Nat := 1393218501833361011046839

theorem tailTrace_8139850 : CollatzResearch.WordTrace tailWord_8139850 prefixEnd_8139850 1393218501833361011046839 := by
  unfold tailWord_8139850
  simp only [CollatzResearch.WordTrace]
  refine ⟨74221179890180275136892251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197923146373814067031712669 74221179890180275136892251)
  ·
    refine ⟨111331769835270412705338377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74221179890180275136892251 111331769835270412705338377)
    ·
      refine ⟨83498827376452809529003783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111331769835270412705338377 83498827376452809529003783)
      ·
        refine ⟨125248241064679214293505675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83498827376452809529003783 125248241064679214293505675)
        ·
          refine ⟨187872361597018821440258513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125248241064679214293505675 187872361597018821440258513)
          ·
            refine ⟨140904271197764116080193885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187872361597018821440258513 140904271197764116080193885)
            ·
              refine ⟨52839101699161543530072707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140904271197764116080193885 52839101699161543530072707)
              ·
                refine ⟨79258652548742315295109061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52839101699161543530072707 79258652548742315295109061)
                ·
                  refine ⟨14860997352889184117832949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79258652548742315295109061 14860997352889184117832949)
                  ·
                    refine ⟨1393218501833361011046839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14860997352889184117832949 1393218501833361011046839)
                    ·
                      rfl

theorem cell23_8139850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_8139850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139850 prefixEnd_8139850 := by exact prefixLift 8139850
  have htrace : WordTrace (prefixWord ++ tailWord_8139850) baseStart_8139850 baseEnd_8139850 := by
    simpa [prefixWord, tailWord_8139850, baseEnd_8139850] using wordTrace_append hprefix tailTrace_8139850
  have hstable : (prefixWord ++ tailWord_8139850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139850).length < 2 ^ (prefixWord ++ tailWord_8139850).sum := by decide
  have hdescent : baseEnd_8139850 < baseStart_8139850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139854 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_8139854 : Nat := 118140960795 + 8139854 * 2 ^ 59
def prefixEnd_8139854 : Nat := 4983230072969 + 3 ^ 40 * 8139854 * 2
def baseEnd_8139854 : Nat := 464406395491411224165611

theorem tailTrace_8139854 : CollatzResearch.WordTrace tailWord_8139854 prefixEnd_8139854 464406395491411224165611 := by
  unfold tailWord_8139854
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110608181588326153839327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197923243635137739487143077 37110608181588326153839327)
  ·
    refine ⟨55665912272382489230758991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37110608181588326153839327 55665912272382489230758991)
    ·
      refine ⟨83498868408573733846138487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55665912272382489230758991 83498868408573733846138487)
      ·
        refine ⟨125248302612860600769207731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83498868408573733846138487 125248302612860600769207731)
        ·
          refine ⟨187872453919290901153811597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125248302612860600769207731 187872453919290901153811597)
          ·
            refine ⟨70452170219734087932679349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187872453919290901153811597 70452170219734087932679349)
            ·
              refine ⟨6604890958100070743688689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70452170219734087932679349 6604890958100070743688689)
              ·
                refine ⟨4953668218575053057766517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604890958100070743688689 4953668218575053057766517)
                ·
                  refine ⟨464406395491411224165611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4953668218575053057766517 464406395491411224165611)
                  ·
                    rfl

theorem cell23_8139854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_8139854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139854 prefixEnd_8139854 := by exact prefixLift 8139854
  have htrace : WordTrace (prefixWord ++ tailWord_8139854) baseStart_8139854 baseEnd_8139854 := by
    simpa [prefixWord, tailWord_8139854, baseEnd_8139854] using wordTrace_append hprefix tailTrace_8139854
  have hstable : (prefixWord ++ tailWord_8139854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139854).length < 2 ^ (prefixWord ++ tailWord_8139854).sum := by decide
  have hdescent : baseEnd_8139854 < baseStart_8139854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139860 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_8139860 : Nat := 118140960795 + 8139860 * 2 ^ 59
def prefixEnd_8139860 : Nat := 4983230072969 + 3 ^ 40 * 8139860 * 2
def baseEnd_8139860 : Nat := 4179660640306627994015471

theorem tailTrace_8139860 : CollatzResearch.WordTrace tailWord_8139860 prefixEnd_8139860 4179660640306627994015471 := by
  unfold tailWord_8139860
  simp only [CollatzResearch.WordTrace]
  refine ⟨148442542145342436127716517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197923389527123248170288689 148442542145342436127716517)
  ·
    refine ⟨27832976652251706773946847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148442542145342436127716517 27832976652251706773946847)
    ·
      refine ⟨41749464978377560160920271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27832976652251706773946847 41749464978377560160920271)
      ·
        refine ⟨62624197467566340241380407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41749464978377560160920271 62624197467566340241380407)
        ·
          refine ⟨93936296201349510362070611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62624197467566340241380407 93936296201349510362070611)
          ·
            refine ⟨140904444302024265543105917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93936296201349510362070611 140904444302024265543105917)
            ·
              refine ⟨52839166613259099578664719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140904444302024265543105917 52839166613259099578664719)
              ·
                refine ⟨79258749919888649367997079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52839166613259099578664719 79258749919888649367997079)
                ·
                  refine ⟨118888124879832974051995619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79258749919888649367997079 118888124879832974051995619)
                  ·
                    refine ⟨178332187319749461077993429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118888124879832974051995619 178332187319749461077993429)
                    ·
                      refine ⟨4179660640306627994015471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178332187319749461077993429 4179660640306627994015471)
                      ·
                        rfl

theorem cell23_8139860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_8139860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139860 prefixEnd_8139860 := by exact prefixLift 8139860
  have htrace : WordTrace (prefixWord ++ tailWord_8139860) baseStart_8139860 baseEnd_8139860 := by
    simpa [prefixWord, tailWord_8139860, baseEnd_8139860] using wordTrace_append hprefix tailTrace_8139860
  have hstable : (prefixWord ++ tailWord_8139860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139860).length < 2 ^ (prefixWord ++ tailWord_8139860).sum := by decide
  have hdescent : baseEnd_8139860 < baseStart_8139860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139887 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_8139887 : Nat := 118140960795 + 8139887 * 2 ^ 59
def prefixEnd_8139887 : Nat := 4983230072969 + 3 ^ 40 * 8139887 * 2
def baseEnd_8139887 : Nat := 4179674504284299388377847

theorem tailTrace_8139887 : CollatzResearch.WordTrace tailWord_8139887 prefixEnd_8139887 4179674504284299388377847 := by
  unfold tailWord_8139887
  simp only [CollatzResearch.WordTrace]
  refine ⟨296886069061587055866665915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197924046041058037244443943 296886069061587055866665915)
  ·
    refine ⟨445329103592380583799998873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296886069061587055866665915 445329103592380583799998873)
    ·
      refine ⟨333996827694285437849999155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445329103592380583799998873 333996827694285437849999155)
      ·
        refine ⟨500995241541428156774998733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333996827694285437849999155 500995241541428156774998733)
        ·
          refine ⟨187873215578035558790624525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500995241541428156774998733 187873215578035558790624525)
          ·
            refine ⟨70452455841763334546484197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187873215578035558790624525 70452455841763334546484197)
            ·
              refine ⟨13209835470330625227465787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70452455841763334546484197 13209835470330625227465787)
              ·
                refine ⟨19814753205495937841198681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13209835470330625227465787 19814753205495937841198681)
                ·
                  refine ⟨14861064904121953380899011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19814753205495937841198681 14861064904121953380899011)
                  ·
                    refine ⟨22291597356182930071348517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14861064904121953380899011 22291597356182930071348517)
                    ·
                      refine ⟨4179674504284299388377847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22291597356182930071348517 4179674504284299388377847)
                      ·
                        rfl

theorem cell23_8139887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_8139887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139887 prefixEnd_8139887 := by exact prefixLift 8139887
  have htrace : WordTrace (prefixWord ++ tailWord_8139887) baseStart_8139887 baseEnd_8139887 := by
    simpa [prefixWord, tailWord_8139887, baseEnd_8139887] using wordTrace_append hprefix tailTrace_8139887
  have hstable : (prefixWord ++ tailWord_8139887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139887).length < 2 ^ (prefixWord ++ tailWord_8139887).sum := by decide
  have hdescent : baseEnd_8139887 < baseStart_8139887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139900 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_8139900 : Nat := 118140960795 + 8139900 * 2 ^ 59
def prefixEnd_8139900 : Nat := 4983230072969 + 3 ^ 40 * 8139900 * 2
def baseEnd_8139900 : Nat := 4179681179532807837515287

theorem tailTrace_8139900 : CollatzResearch.WordTrace tailWord_8139900 prefixEnd_8139900 4179681179532807837515287 := by
  unfold tailWord_8139900
  simp only [CollatzResearch.WordTrace]
  refine ⟨148443271605269979543444577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197924362140359972724592769 148443271605269979543444577)
  ·
    refine ⟨111332453703952484657583433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148443271605269979543444577 111332453703952484657583433)
    ·
      refine ⟨83499340277964363493187575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111332453703952484657583433 83499340277964363493187575)
      ·
        refine ⟨125249010416946545239781363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83499340277964363493187575 125249010416946545239781363)
        ·
          refine ⟨187873515625419817859672045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125249010416946545239781363 187873515625419817859672045)
          ·
            refine ⟨70452568359532431697377017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187873515625419817859672045 70452568359532431697377017)
            ·
              refine ⟨52839426269649323773032763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70452568359532431697377017 52839426269649323773032763)
              ·
                refine ⟨79259139404473985659549145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52839426269649323773032763 79259139404473985659549145)
                ·
                  refine ⟨59444354553355489244661859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79259139404473985659549145 59444354553355489244661859)
                  ·
                    refine ⟨89166531830033233866992789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59444354553355489244661859 89166531830033233866992789)
                    ·
                      refine ⟨4179681179532807837515287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89166531830033233866992789 4179681179532807837515287)
                      ·
                        rfl

theorem cell23_8139900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_8139900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139900 prefixEnd_8139900 := by exact prefixLift 8139900
  have htrace : WordTrace (prefixWord ++ tailWord_8139900) baseStart_8139900 baseEnd_8139900 := by
    simpa [prefixWord, tailWord_8139900, baseEnd_8139900] using wordTrace_append hprefix tailTrace_8139900
  have hstable : (prefixWord ++ tailWord_8139900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139900).length < 2 ^ (prefixWord ++ tailWord_8139900).sum := by decide
  have hdescent : baseEnd_8139900 < baseStart_8139900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139907 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 3]
def baseStart_8139907 : Nat := 118140960795 + 8139907 * 2 ^ 59
def prefixEnd_8139907 : Nat := 4983230072969 + 3 ^ 40 * 8139907 * 2
def baseEnd_8139907 : Nat := 4179684773897389310127755

theorem tailTrace_8139907 : CollatzResearch.WordTrace tailWord_8139907 prefixEnd_8139907 4179684773897389310127755 := by
  unfold tailWord_8139907
  simp only [CollatzResearch.WordTrace]
  refine ⟨296886798521514599282393975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197924532347676399521595983 296886798521514599282393975)
  ·
    refine ⟨445330197782271898923590963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296886798521514599282393975 445330197782271898923590963)
    ·
      refine ⟨667995296673407848385386445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445330197782271898923590963 667995296673407848385386445)
      ·
        refine ⟨250498236252527943144519917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667995296673407848385386445 250498236252527943144519917)
        ·
          refine ⟨93936838594697978679194969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250498236252527943144519917 93936838594697978679194969)
          ·
            refine ⟨70452628946023484009396227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93936838594697978679194969 70452628946023484009396227)
            ·
              refine ⟨105678943419035226014094341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70452628946023484009396227 105678943419035226014094341)
              ·
                refine ⟨19814801891069104877642689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105678943419035226014094341 19814801891069104877642689)
                ·
                  refine ⟨14861101418301828658232017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19814801891069104877642689 14861101418301828658232017)
                  ·
                    refine ⟨11145826063726371493674013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14861101418301828658232017 11145826063726371493674013)
                    ·
                      refine ⟨4179684773897389310127755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11145826063726371493674013 4179684773897389310127755)
                      ·
                        rfl

theorem cell23_8139907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_8139907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139907 prefixEnd_8139907 := by exact prefixLift 8139907
  have htrace : WordTrace (prefixWord ++ tailWord_8139907) baseStart_8139907 baseEnd_8139907 := by
    simpa [prefixWord, tailWord_8139907, baseEnd_8139907] using wordTrace_append hprefix tailTrace_8139907
  have hstable : (prefixWord ++ tailWord_8139907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139907).length < 2 ^ (prefixWord ++ tailWord_8139907).sum := by decide
  have hdescent : baseEnd_8139907 < baseStart_8139907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139927 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 6]
def baseStart_8139927 : Nat := 118140960795 + 8139927 * 2 ^ 59
def prefixEnd_8139927 : Nat := 4983230072969 + 3 ^ 40 * 8139927 * 2
def baseEnd_8139927 : Nat := 464410560390053247986407

theorem tailTrace_8139927 : CollatzResearch.WordTrace tailWord_8139927 prefixEnd_8139927 464410560390053247986407 := by
  unfold tailWord_8139927
  simp only [CollatzResearch.WordTrace]
  refine ⟨296887527981442142698122035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197925018654294761798748023 296887527981442142698122035)
  ·
    refine ⟨445331291972163214047183053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296887527981442142698122035 445331291972163214047183053)
    ·
      refine ⟨166999234489561205267693645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445331291972163214047183053 166999234489561205267693645)
      ·
        refine ⟨62624712933585451975385117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166999234489561205267693645 62624712933585451975385117)
        ·
          refine ⟨23484267350094544490769419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62624712933585451975385117 23484267350094544490769419)
          ·
            refine ⟨35226401025141816736154129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23484267350094544490769419 35226401025141816736154129)
            ·
              refine ⟨26419800768856362552115597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35226401025141816736154129 26419800768856362552115597)
              ·
                refine ⟨9907425288321135957043349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26419800768856362552115597 9907425288321135957043349)
                ·
                  refine ⟨464410560390053247986407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9907425288321135957043349 464410560390053247986407)
                  ·
                    rfl

theorem cell23_8139927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 6].length) (baseStart_8139927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139927 prefixEnd_8139927 := by exact prefixLift 8139927
  have htrace : WordTrace (prefixWord ++ tailWord_8139927) baseStart_8139927 baseEnd_8139927 := by
    simpa [prefixWord, tailWord_8139927, baseEnd_8139927] using wordTrace_append hprefix tailTrace_8139927
  have hstable : (prefixWord ++ tailWord_8139927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139927).length < 2 ^ (prefixWord ++ tailWord_8139927).sum := by decide
  have hdescent : baseEnd_8139927 < baseStart_8139927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8139938 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_8139938 : Nat := 118140960795 + 8139938 * 2 ^ 59
def prefixEnd_8139938 : Nat := 4983230072969 + 3 ^ 40 * 8139938 * 2
def baseEnd_8139938 : Nat := 4179700691797678688840113

theorem tailTrace_8139938 : CollatzResearch.WordTrace tailWord_8139938 prefixEnd_8139938 4179700691797678688840113 := by
  unfold tailWord_8139938
  simp only [CollatzResearch.WordTrace]
  refine ⟨74221982296100572894193117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197925286122934861051181645 74221982296100572894193117)
  ·
    refine ⟨27833243361037714835322419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74221982296100572894193117 27833243361037714835322419)
    ·
      refine ⟨41749865041556572252983629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27833243361037714835322419 41749865041556572252983629)
      ·
        refine ⟨15656199390583714594868861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41749865041556572252983629 15656199390583714594868861)
        ·
          refine ⟨5871074771468892973075823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15656199390583714594868861 5871074771468892973075823)
          ·
            refine ⟨8806612157203339459613735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871074771468892973075823 8806612157203339459613735)
            ·
              refine ⟨13209918235805009189420603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806612157203339459613735 13209918235805009189420603)
              ·
                refine ⟨19814877353707513784130905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13209918235805009189420603 19814877353707513784130905)
                ·
                  refine ⟨14861158015280635338098179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19814877353707513784130905 14861158015280635338098179)
                  ·
                    refine ⟨22291737022920953007147269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14861158015280635338098179 22291737022920953007147269)
                    ·
                      refine ⟨4179700691797678688840113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22291737022920953007147269 4179700691797678688840113)
                      ·
                        rfl

theorem cell23_8139938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_8139938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8139938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8139938 prefixEnd_8139938 := by exact prefixLift 8139938
  have htrace : WordTrace (prefixWord ++ tailWord_8139938) baseStart_8139938 baseEnd_8139938 := by
    simpa [prefixWord, tailWord_8139938, baseEnd_8139938] using wordTrace_append hprefix tailTrace_8139938
  have hstable : (prefixWord ++ tailWord_8139938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8139938).length < 2 ^ (prefixWord ++ tailWord_8139938).sum := by decide
  have hdescent : baseEnd_8139938 < baseStart_8139938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8139938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140005 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 1, 1, 3]
def baseStart_8140005 : Nat := 118140960795 + 8140005 * 2 ^ 59
def prefixEnd_8140005 : Nat := 4983230072969 + 3 ^ 40 * 8140005 * 2
def baseEnd_8140005 : Nat := 4179735095001529926702305

theorem tailTrace_8140005 : CollatzResearch.WordTrace tailWord_8140005 prefixEnd_8140005 4179735095001529926702305 := by
  unfold tailWord_8140005
  simp only [CollatzResearch.WordTrace]
  refine ⟨296890372875159562019461469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197926915250106374679640979 296890372875159562019461469)
  ·
    refine ⟨111333889828184835757298051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296890372875159562019461469 111333889828184835757298051)
    ·
      refine ⟨167000834742277253635947077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111333889828184835757298051 167000834742277253635947077)
      ·
        refine ⟨31312656514176985056740077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167000834742277253635947077 31312656514176985056740077)
        ·
          refine ⟨11742246192816369396277529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31312656514176985056740077 11742246192816369396277529)
          ·
            refine ⟨8806684644612277047208147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11742246192816369396277529 8806684644612277047208147)
            ·
              refine ⟨13210026966918415570812221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806684644612277047208147 13210026966918415570812221)
              ·
                refine ⟨4953760112594405839054583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13210026966918415570812221 4953760112594405839054583)
                ·
                  refine ⟨7430640168891608758581875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953760112594405839054583 7430640168891608758581875)
                  ·
                    refine ⟨11145960253337413137872813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7430640168891608758581875 11145960253337413137872813)
                    ·
                      refine ⟨4179735095001529926702305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11145960253337413137872813 4179735095001529926702305)
                      ·
                        rfl

theorem cell23_8140005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_8140005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140005 prefixEnd_8140005 := by exact prefixLift 8140005
  have htrace : WordTrace (prefixWord ++ tailWord_8140005) baseStart_8140005 baseEnd_8140005 := by
    simpa [prefixWord, tailWord_8140005, baseEnd_8140005] using wordTrace_append hprefix tailTrace_8140005
  have hstable : (prefixWord ++ tailWord_8140005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140005).length < 2 ^ (prefixWord ++ tailWord_8140005).sum := by decide
  have hdescent : baseEnd_8140005 < baseStart_8140005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140061 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_8140061 : Nat := 118140960795 + 8140061 * 2 ^ 59
def prefixEnd_8140061 : Nat := 4983230072969 + 3 ^ 40 * 8140061 * 2
def baseEnd_8140061 : Nat := 4179763849918181707602047

theorem tailTrace_8140061 : CollatzResearch.WordTrace tailWord_8140061 prefixEnd_8140061 4179763849918181707602047 := by
  unfold tailWord_8140061
  simp only [CollatzResearch.WordTrace]
  refine ⟨296892415362956683583500037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197928276908637789055666691 296892415362956683583500037)
  ·
    refine ⟨55667327880554378171906257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296892415362956683583500037 55667327880554378171906257)
    ·
      refine ⟨41750495910415783628929693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55667327880554378171906257 41750495910415783628929693)
      ·
        refine ⟨15656435966405918860848635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41750495910415783628929693 15656435966405918860848635)
        ·
          refine ⟨23484653949608878291272953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656435966405918860848635 23484653949608878291272953)
          ·
            refine ⟨17613490462206658718454715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23484653949608878291272953 17613490462206658718454715)
            ·
              refine ⟨26420235693309988077682073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17613490462206658718454715 26420235693309988077682073)
              ·
                refine ⟨19815176769982491058261555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26420235693309988077682073 19815176769982491058261555)
                ·
                  refine ⟨29722765154973736587392333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19815176769982491058261555 29722765154973736587392333)
                  ·
                    refine ⟨11146036933115151220272125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29722765154973736587392333 11146036933115151220272125)
                    ·
                      refine ⟨4179763849918181707602047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11146036933115151220272125 4179763849918181707602047)
                      ·
                        rfl

theorem cell23_8140061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_8140061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140061 prefixEnd_8140061 := by exact prefixLift 8140061
  have htrace : WordTrace (prefixWord ++ tailWord_8140061) baseStart_8140061 baseEnd_8140061 := by
    simpa [prefixWord, tailWord_8140061, baseEnd_8140061] using wordTrace_append hprefix tailTrace_8140061
  have hstable : (prefixWord ++ tailWord_8140061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140061).length < 2 ^ (prefixWord ++ tailWord_8140061).sum := by decide
  have hdescent : baseEnd_8140061 < baseStart_8140061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140084 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_8140084 : Nat := 118140960795 + 8140084 * 2 ^ 59
def prefixEnd_8140084 : Nat := 4983230072969 + 3 ^ 40 * 8140084 * 2
def baseEnd_8140084 : Nat := 4179775659973235117614441

theorem tailTrace_8140084 : CollatzResearch.WordTrace tailWord_8140084 prefixEnd_8140084 4179775659973235117614441 := by
  unfold tailWord_8140084
  simp only [CollatzResearch.WordTrace]
  refine ⟨148446627120936679255793653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197928836161248905674391537 148446627120936679255793653)
  ·
    refine ⟨13916871292587813680230655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148446627120936679255793653 13916871292587813680230655)
    ·
      refine ⟨20875306938881720520345983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13916871292587813680230655 20875306938881720520345983)
      ·
        refine ⟨31312960408322580780518975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20875306938881720520345983 31312960408322580780518975)
        ·
          refine ⟨46969440612483871170778463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31312960408322580780518975 46969440612483871170778463)
          ·
            refine ⟨70454160918725806756167695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46969440612483871170778463 70454160918725806756167695)
            ·
              refine ⟨105681241378088710134251543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70454160918725806756167695 105681241378088710134251543)
              ·
                refine ⟨158521862067133065201377315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105681241378088710134251543 158521862067133065201377315)
                ·
                  refine ⟨237782793100699597802065973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158521862067133065201377315 237782793100699597802065973)
                  ·
                    refine ⟨22292136853190587293943685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237782793100699597802065973 22292136853190587293943685)
                    ·
                      refine ⟨4179775659973235117614441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22292136853190587293943685 4179775659973235117614441)
                      ·
                        rfl

theorem cell23_8140084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_8140084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140084 prefixEnd_8140084 := by exact prefixLift 8140084
  have htrace : WordTrace (prefixWord ++ tailWord_8140084) baseStart_8140084 baseEnd_8140084 := by
    simpa [prefixWord, tailWord_8140084, baseEnd_8140084] using wordTrace_append hprefix tailTrace_8140084
  have hstable : (prefixWord ++ tailWord_8140084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140084).length < 2 ^ (prefixWord ++ tailWord_8140084).sum := by decide
  have hdescent : baseEnd_8140084 < baseStart_8140084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140094 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_8140094 : Nat := 118140960795 + 8140094 * 2 ^ 59
def prefixEnd_8140094 : Nat := 4983230072969 + 3 ^ 40 * 8140094 * 2
def baseEnd_8140094 : Nat := 1393260264926593359496465

theorem tailTrace_8140094 : CollatzResearch.WordTrace tailWord_8140094 prefixEnd_8140094 1393260264926593359496465 := by
  unfold tailWord_8140094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111702371479641277431417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197929079314558086812967557 37111702371479641277431417)
  ·
    refine ⟨27833776778609730958073563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37111702371479641277431417 27833776778609730958073563)
    ·
      refine ⟨41750665167914596437110345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27833776778609730958073563 41750665167914596437110345)
      ·
        refine ⟨31312998875935947327832759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41750665167914596437110345 31312998875935947327832759)
        ·
          refine ⟨46969498313903920991749139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31312998875935947327832759 46969498313903920991749139)
          ·
            refine ⟨70454247470855881487623709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46969498313903920991749139 70454247470855881487623709)
            ·
              refine ⟨26420342801570955557858891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70454247470855881487623709 26420342801570955557858891)
              ·
                refine ⟨39630514202356433336788337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26420342801570955557858891 39630514202356433336788337)
                ·
                  refine ⟨29722885651767325002591253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39630514202356433336788337 29722885651767325002591253)
                  ·
                    refine ⟨1393260264926593359496465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29722885651767325002591253 1393260264926593359496465)
                    ·
                      rfl

theorem cell23_8140094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_8140094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140094 prefixEnd_8140094 := by exact prefixLift 8140094
  have htrace : WordTrace (prefixWord ++ tailWord_8140094) baseStart_8140094 baseEnd_8140094 := by
    simpa [prefixWord, tailWord_8140094, baseEnd_8140094] using wordTrace_append hprefix tailTrace_8140094
  have hstable : (prefixWord ++ tailWord_8140094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140094).length < 2 ^ (prefixWord ++ tailWord_8140094).sum := by decide
  have hdescent : baseEnd_8140094 < baseStart_8140094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140141 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 5]
def baseStart_8140141 : Nat := 118140960795 + 8140141 * 2 ^ 59
def prefixEnd_8140141 : Nat := 4983230072969 + 3 ^ 40 * 8140141 * 2
def baseEnd_8140141 : Nat := 464422769818949043844631

theorem tailTrace_8140141 : CollatzResearch.WordTrace tailWord_8140141 prefixEnd_8140141 464422769818949043844631 := by
  unfold tailWord_8140141
  simp only [CollatzResearch.WordTrace]
  refine ⟨296895333202666857246412277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197930222135111238164274851 296895333202666857246412277)
  ·
    refine ⟨27833937487750017866851151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296895333202666857246412277 27833937487750017866851151)
    ·
      refine ⟨41750906231625026800276727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27833937487750017866851151 41750906231625026800276727)
      ·
        refine ⟨62626359347437540200415091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41750906231625026800276727 62626359347437540200415091)
        ·
          refine ⟨93939539021156310300622637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62626359347437540200415091 93939539021156310300622637)
          ·
            refine ⟨35227327132933616362733489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93939539021156310300622637 35227327132933616362733489)
            ·
              refine ⟨26420495349700212272050117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35227327132933616362733489 26420495349700212272050117)
              ·
                refine ⟨4953842878068789801009397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26420495349700212272050117 4953842878068789801009397)
                ·
                  refine ⟨464422769818949043844631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4953842878068789801009397 464422769818949043844631)
                  ·
                    rfl

theorem cell23_8140141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_8140141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140141 prefixEnd_8140141 := by exact prefixLift 8140141
  have htrace : WordTrace (prefixWord ++ tailWord_8140141) baseStart_8140141 baseEnd_8140141 := by
    simpa [prefixWord, tailWord_8140141, baseEnd_8140141] using wordTrace_append hprefix tailTrace_8140141
  have hstable : (prefixWord ++ tailWord_8140141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140141).length < 2 ^ (prefixWord ++ tailWord_8140141).sum := by decide
  have hdescent : baseEnd_8140141 < baseStart_8140141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140188 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_8140188 : Nat := 118140960795 + 8140188 * 2 ^ 59
def prefixEnd_8140188 : Nat := 4983230072969 + 3 ^ 40 * 8140188 * 2
def baseEnd_8140188 : Nat := 1393276353987100903571321

theorem tailTrace_8140188 : CollatzResearch.WordTrace tailWord_8140188 prefixEnd_8140188 1393276353987100903571321 := by
  unfold tailWord_8140188
  simp only [CollatzResearch.WordTrace]
  refine ⟨148448523716748292136686609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197931364955664389515582145 148448523716748292136686609)
  ·
    refine ⟨111336392787561219102514957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148448523716748292136686609 111336392787561219102514957)
    ·
      refine ⟨41751147295335457163443109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111336392787561219102514957 41751147295335457163443109)
      ·
        refine ⟨7828340117875398218145583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41751147295335457163443109 7828340117875398218145583)
        ·
          refine ⟨11742510176813097327218375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7828340117875398218145583 11742510176813097327218375)
          ·
            refine ⟨17613765265219645990827563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742510176813097327218375 17613765265219645990827563)
            ·
              refine ⟨26420647897829468986241345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17613765265219645990827563 26420647897829468986241345)
              ·
                refine ⟨19815485923372101739681009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26420647897829468986241345 19815485923372101739681009)
                ·
                  refine ⟨14861614442529076304760757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19815485923372101739681009 14861614442529076304760757)
                  ·
                    refine ⟨1393276353987100903571321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14861614442529076304760757 1393276353987100903571321)
                    ·
                      rfl

theorem cell23_8140188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_8140188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140188 prefixEnd_8140188 := by exact prefixLift 8140188
  have htrace : WordTrace (prefixWord ++ tailWord_8140188) baseStart_8140188 baseEnd_8140188 := by
    simpa [prefixWord, tailWord_8140188, baseEnd_8140188] using wordTrace_append hprefix tailTrace_8140188
  have hstable : (prefixWord ++ tailWord_8140188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140188).length < 2 ^ (prefixWord ++ tailWord_8140188).sum := by decide
  have hdescent : baseEnd_8140188 < baseStart_8140188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140191 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_8140191 : Nat := 118140960795 + 8140191 * 2 ^ 59
def prefixEnd_8140191 : Nat := 4983230072969 + 3 ^ 40 * 8140191 * 2
def baseEnd_8140191 : Nat := 4179830602403266198976449

theorem tailTrace_8140191 : CollatzResearch.WordTrace tailWord_8140191 prefixEnd_8140191 4179830602403266198976449 := by
  unfold tailWord_8140191
  simp only [CollatzResearch.WordTrace]
  refine ⟨296897156852485715785732427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197931437901657143857154951 296897156852485715785732427)
  ·
    refine ⟨445345735278728573678598641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296897156852485715785732427 445345735278728573678598641)
    ·
      refine ⟨334009301459046430258948981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445345735278728573678598641 334009301459046430258948981)
      ·
        refine ⟨31313372011785602836776467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334009301459046430258948981 31313372011785602836776467)
        ·
          refine ⟨46970058017678404255164701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31313372011785602836776467 46970058017678404255164701)
          ·
            refine ⟨17613771756629401595686763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46970058017678404255164701 17613771756629401595686763)
            ·
              refine ⟨26420657634944102393530145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17613771756629401595686763 26420657634944102393530145)
              ·
                refine ⟨19815493226208076795147609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26420657634944102393530145 19815493226208076795147609)
                ·
                  refine ⟨14861619919656057596360707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19815493226208076795147609 14861619919656057596360707)
                  ·
                    refine ⟨22292429879484086394541061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14861619919656057596360707 22292429879484086394541061)
                    ·
                      refine ⟨4179830602403266198976449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22292429879484086394541061 4179830602403266198976449)
                      ·
                        rfl

theorem cell23_8140191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_8140191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140191 prefixEnd_8140191 := by exact prefixLift 8140191
  have htrace : WordTrace (prefixWord ++ tailWord_8140191) baseStart_8140191 baseEnd_8140191 := by
    simpa [prefixWord, tailWord_8140191, baseEnd_8140191] using wordTrace_append hprefix tailTrace_8140191
  have hstable : (prefixWord ++ tailWord_8140191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140191).length < 2 ^ (prefixWord ++ tailWord_8140191).sum := by decide
  have hdescent : baseEnd_8140191 < baseStart_8140191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140224 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_8140224 : Nat := 118140960795 + 8140224 * 2 ^ 59
def prefixEnd_8140224 : Nat := 4983230072969 + 3 ^ 40 * 8140224 * 2
def baseEnd_8140224 : Nat := 4179847547264864569863797

theorem tailTrace_8140224 : CollatzResearch.WordTrace tailWord_8140224 prefixEnd_8140224 4179847547264864569863797 := by
  unfold tailWord_8140224
  simp only [CollatzResearch.WordTrace]
  refine ⟨148449180230683081210841863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197932240307577441614455817 148449180230683081210841863)
  ·
    refine ⟨222673770346024621816262795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148449180230683081210841863 222673770346024621816262795)
    ·
      refine ⟨334010655519036932724394193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222673770346024621816262795 334010655519036932724394193)
      ·
        refine ⟨250507991639277699543295645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334010655519036932724394193 250507991639277699543295645)
        ·
          refine ⟨93940496864729137328735867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250507991639277699543295645 93940496864729137328735867)
          ·
            refine ⟨140910745297093705993103801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93940496864729137328735867 140910745297093705993103801)
            ·
              refine ⟨105683058972820279494827851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140910745297093705993103801 105683058972820279494827851)
              ·
                refine ⟨158524588459230419242241777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105683058972820279494827851 158524588459230419242241777)
                ·
                  refine ⟨118893441344422814431681333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158524588459230419242241777 118893441344422814431681333)
                  ·
                    refine ⟨11146260126039638852970125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118893441344422814431681333 11146260126039638852970125)
                    ·
                      refine ⟨4179847547264864569863797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11146260126039638852970125 4179847547264864569863797)
                      ·
                        rfl

theorem cell23_8140224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_8140224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140224 prefixEnd_8140224 := by exact prefixLift 8140224
  have htrace : WordTrace (prefixWord ++ tailWord_8140224) baseStart_8140224 baseEnd_8140224 := by
    simpa [prefixWord, tailWord_8140224, baseEnd_8140224] using wordTrace_append hprefix tailTrace_8140224
  have hstable : (prefixWord ++ tailWord_8140224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140224).length < 2 ^ (prefixWord ++ tailWord_8140224).sum := by decide
  have hdescent : baseEnd_8140224 < baseStart_8140224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140228 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_8140228 : Nat := 118140960795 + 8140228 * 2 ^ 59
def prefixEnd_8140228 : Nat := 4983230072969 + 3 ^ 40 * 8140228 * 2
def baseEnd_8140228 : Nat := 4179849601187482554213779

theorem tailTrace_8140228 : CollatzResearch.WordTrace tailWord_8140228 prefixEnd_8140228 4179849601187482554213779 := by
  unfold tailWord_8140228
  simp only [CollatzResearch.WordTrace]
  refine ⟨148449253176675835552414669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197932337568901114069886225 148449253176675835552414669)
  ·
    refine ⟨55668469941253438332155501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148449253176675835552414669 55668469941253438332155501)
    ·
      refine ⟨20875676227970039374558313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55668469941253438332155501 20875676227970039374558313)
      ·
        refine ⟨15656757170977529530918735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20875676227970039374558313 15656757170977529530918735)
        ·
          refine ⟨23485135756466294296378103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656757170977529530918735 23485135756466294296378103)
          ·
            refine ⟨35227703634699441444567155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23485135756466294296378103 35227703634699441444567155)
            ·
              refine ⟨52841555452049162166850733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35227703634699441444567155 52841555452049162166850733)
              ·
                refine ⟨19815583294518435812569025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52841555452049162166850733 19815583294518435812569025)
                ·
                  refine ⟨14861687470888826859426769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19815583294518435812569025 14861687470888826859426769)
                  ·
                    refine ⟨11146265603166620144570077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14861687470888826859426769 11146265603166620144570077)
                    ·
                      refine ⟨4179849601187482554213779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11146265603166620144570077 4179849601187482554213779)
                      ·
                        rfl

theorem cell23_8140228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_8140228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140228 prefixEnd_8140228 := by exact prefixLift 8140228
  have htrace : WordTrace (prefixWord ++ tailWord_8140228) baseStart_8140228 baseEnd_8140228 := by
    simpa [prefixWord, tailWord_8140228, baseEnd_8140228] using wordTrace_append hprefix tailTrace_8140228
  have hstable : (prefixWord ++ tailWord_8140228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140228).length < 2 ^ (prefixWord ++ tailWord_8140228).sum := by decide
  have hdescent : baseEnd_8140228 < baseStart_8140228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140261 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_8140261 : Nat := 118140960795 + 8140261 * 2 ^ 59
def prefixEnd_8140261 : Nat := 4983230072969 + 3 ^ 40 * 8140261 * 2
def baseEnd_8140261 : Nat := 1393288848683026975033709

theorem tailTrace_8140261 : CollatzResearch.WordTrace tailWord_8140261 prefixEnd_8140261 1393288848683026975033709 := by
  unfold tailWord_8140261
  simp only [CollatzResearch.WordTrace]
  refine ⟨296899709962232117740780637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197933139974821411827187091 296899709962232117740780637)
  ·
    refine ⟨111337391235837044152792739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296899709962232117740780637 111337391235837044152792739)
    ·
      refine ⟨167006086853755566229189109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111337391235837044152792739 167006086853755566229189109)
      ·
        refine ⟨15656820642539584333986479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167006086853755566229189109 15656820642539584333986479)
        ·
          refine ⟨23485230963809376500979719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656820642539584333986479 23485230963809376500979719)
          ·
            refine ⟨35227846445714064751469579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23485230963809376500979719 35227846445714064751469579)
            ·
              refine ⟨52841769668571097127204369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35227846445714064751469579 52841769668571097127204369)
              ·
                refine ⟨39631327251428322845403277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52841769668571097127204369 39631327251428322845403277)
                ·
                  refine ⟨14861747719285621067026229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39631327251428322845403277 14861747719285621067026229)
                  ·
                    refine ⟨1393288848683026975033709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14861747719285621067026229 1393288848683026975033709)
                    ·
                      rfl

theorem cell23_8140261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_8140261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140261 prefixEnd_8140261 := by exact prefixLift 8140261
  have htrace : WordTrace (prefixWord ++ tailWord_8140261) baseStart_8140261 baseEnd_8140261 := by
    simpa [prefixWord, tailWord_8140261, baseEnd_8140261] using wordTrace_append hprefix tailTrace_8140261
  have hstable : (prefixWord ++ tailWord_8140261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140261).length < 2 ^ (prefixWord ++ tailWord_8140261).sum := by decide
  have hdescent : baseEnd_8140261 < baseStart_8140261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140281 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 4]
def baseStart_8140281 : Nat := 118140960795 + 8140281 * 2 ^ 59
def prefixEnd_8140281 : Nat := 4983230072969 + 3 ^ 40 * 8140281 * 2
def baseEnd_8140281 : Nat := 4179876815662170846851035

theorem tailTrace_8140281 : CollatzResearch.WordTrace tailWord_8140281 prefixEnd_8140281 4179876815662170846851035 := by
  unfold tailWord_8140281
  simp only [CollatzResearch.WordTrace]
  refine ⟨296900439422159661156508697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197933626281439774104339131 296900439422159661156508697)
  ·
    refine ⟨222675329566619745867381523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296900439422159661156508697 222675329566619745867381523)
    ·
      refine ⟨334012994349929618801072285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222675329566619745867381523 334012994349929618801072285)
      ·
        refine ⟨125254872881223607050402107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334012994349929618801072285 125254872881223607050402107)
        ·
          refine ⟨187882309321835410575603161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125254872881223607050402107 187882309321835410575603161)
          ·
            refine ⟨140911731991376557931702371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187882309321835410575603161 140911731991376557931702371)
            ·
              refine ⟨211367597987064836897553557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140911731991376557931702371 211367597987064836897553557)
              ·
                refine ⟨9907856155643664229572823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211367597987064836897553557 9907856155643664229572823)
                ·
                  refine ⟨14861784233465496344359235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9907856155643664229572823 14861784233465496344359235)
                  ·
                    refine ⟨22292676350198244516538853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14861784233465496344359235 22292676350198244516538853)
                    ·
                      refine ⟨4179876815662170846851035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22292676350198244516538853 4179876815662170846851035)
                      ·
                        rfl

theorem cell23_8140281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_8140281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140281 prefixEnd_8140281 := by exact prefixLift 8140281
  have htrace : WordTrace (prefixWord ++ tailWord_8140281) baseStart_8140281 baseEnd_8140281 := by
    simpa [prefixWord, tailWord_8140281, baseEnd_8140281] using wordTrace_append hprefix tailTrace_8140281
  have hstable : (prefixWord ++ tailWord_8140281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140281).length < 2 ^ (prefixWord ++ tailWord_8140281).sum := by decide
  have hdescent : baseEnd_8140281 < baseStart_8140281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140285 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_8140285 : Nat := 118140960795 + 8140285 * 2 ^ 59
def prefixEnd_8140285 : Nat := 4983230072969 + 3 ^ 40 * 8140285 * 2
def baseEnd_8140285 : Nat := 4179878869584788831201017

theorem tailTrace_8140285 : CollatzResearch.WordTrace tailWord_8140285 prefixEnd_8140285 4179878869584788831201017 := by
  unfold tailWord_8140285
  simp only [CollatzResearch.WordTrace]
  refine ⟨296900585314145169839654309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197933723542763446559769539 296900585314145169839654309)
  ·
    refine ⟨55668859746402219344935183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296900585314145169839654309 55668859746402219344935183)
    ·
      refine ⟨83503289619603329017402775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55668859746402219344935183 83503289619603329017402775)
      ·
        refine ⟨125254934429404993526104163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83503289619603329017402775 125254934429404993526104163)
        ·
          refine ⟨187882401644107490289156245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125254934429404993526104163 187882401644107490289156245)
          ·
            refine ⟨8806987577067538607304199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187882401644107490289156245 8806987577067538607304199)
            ·
              refine ⟨13210481365601307910956299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806987577067538607304199 13210481365601307910956299)
              ·
                refine ⟨19815722048401961866434449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13210481365601307910956299 19815722048401961866434449)
                ·
                  refine ⟨14861791536301471399825837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19815722048401961866434449 14861791536301471399825837)
                  ·
                    refine ⟨5573171826113051774934689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14861791536301471399825837 5573171826113051774934689)
                    ·
                      refine ⟨4179878869584788831201017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573171826113051774934689 4179878869584788831201017)
                      ·
                        rfl

theorem cell23_8140285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_8140285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140285 prefixEnd_8140285 := by exact prefixLift 8140285
  have htrace : WordTrace (prefixWord ++ tailWord_8140285) baseStart_8140285 baseEnd_8140285 := by
    simpa [prefixWord, tailWord_8140285, baseEnd_8140285] using wordTrace_append hprefix tailTrace_8140285
  have hstable : (prefixWord ++ tailWord_8140285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140285).length < 2 ^ (prefixWord ++ tailWord_8140285).sum := by decide
  have hdescent : baseEnd_8140285 < baseStart_8140285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140295 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 1, 5]
def baseStart_8140295 : Nat := 118140960795 + 8140295 * 2 ^ 59
def prefixEnd_8140295 : Nat := 4983230072969 + 3 ^ 40 * 8140295 * 2
def baseEnd_8140295 : Nat := 1393294668130444597358657

theorem tailTrace_8140295 : CollatzResearch.WordTrace tailWord_8140295 prefixEnd_8140295 1393294668130444597358657 := by
  unfold tailWord_8140295
  simp only [CollatzResearch.WordTrace]
  refine ⟨296900950044108941547518339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197933966696072627698345559 296900950044108941547518339)
  ·
    refine ⟨445351425066163412321277509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296900950044108941547518339 445351425066163412321277509)
    ·
      refine ⟨83503392199905639810239533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445351425066163412321277509 83503392199905639810239533)
      ·
        refine ⟨31313772074964614928839825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83503392199905639810239533 31313772074964614928839825)
        ·
          refine ⟨23485329056223461196629869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31313772074964614928839825 23485329056223461196629869)
          ·
            refine ⟨8806998396083797948736201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23485329056223461196629869 8806998396083797948736201)
            ·
              refine ⟨6605248797062848461552151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806998396083797948736201 6605248797062848461552151)
              ·
                refine ⟨9907873195594272692328227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605248797062848461552151 9907873195594272692328227)
                ·
                  refine ⟨14861809793391409038492341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9907873195594272692328227 14861809793391409038492341)
                  ·
                    refine ⟨1393294668130444597358657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14861809793391409038492341 1393294668130444597358657)
                    ·
                      rfl

theorem cell23_8140295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_8140295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140295 prefixEnd_8140295 := by exact prefixLift 8140295
  have htrace : WordTrace (prefixWord ++ tailWord_8140295) baseStart_8140295 baseEnd_8140295 := by
    simpa [prefixWord, tailWord_8140295, baseEnd_8140295] using wordTrace_append hprefix tailTrace_8140295
  have hstable : (prefixWord ++ tailWord_8140295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140295).length < 2 ^ (prefixWord ++ tailWord_8140295).sum := by decide
  have hdescent : baseEnd_8140295 < baseStart_8140295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140298 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_8140298 : Nat := 118140960795 + 8140298 * 2 ^ 59
def prefixEnd_8140298 : Nat := 4983230072969 + 3 ^ 40 * 8140298 * 2
def baseEnd_8140298 : Nat := 4179885544833297280338457

theorem tailTrace_8140298 : CollatzResearch.WordTrace tailWord_8140298 prefixEnd_8140298 4179885544833297280338457 := by
  unfold tailWord_8140298
  simp only [CollatzResearch.WordTrace]
  refine ⟨74225264865774518264969387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197934039642065382039918365 74225264865774518264969387)
  ·
    refine ⟨111337897298661777397454081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74225264865774518264969387 111337897298661777397454081)
    ·
      refine ⟨83503422973996333048090561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111337897298661777397454081 83503422973996333048090561)
      ·
        refine ⟨62627567230497249786067921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83503422973996333048090561 62627567230497249786067921)
        ·
          refine ⟨46970675422872937339550941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62627567230497249786067921 46970675422872937339550941)
          ·
            refine ⟨17614003283577351502331603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46970675422872937339550941 17614003283577351502331603)
            ·
              refine ⟨26421004925366027253497405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17614003283577351502331603 26421004925366027253497405)
              ·
                refine ⟨9907876847012260220061527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26421004925366027253497405 9907876847012260220061527)
                ·
                  refine ⟨14861815270518390330092291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9907876847012260220061527 14861815270518390330092291)
                  ·
                    refine ⟨22292722905777585495138437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14861815270518390330092291 22292722905777585495138437)
                    ·
                      refine ⟨4179885544833297280338457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22292722905777585495138437 4179885544833297280338457)
                      ·
                        rfl

theorem cell23_8140298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_8140298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140298 prefixEnd_8140298 := by exact prefixLift 8140298
  have htrace : WordTrace (prefixWord ++ tailWord_8140298) baseStart_8140298 baseEnd_8140298 := by
    simpa [prefixWord, tailWord_8140298, baseEnd_8140298] using wordTrace_append hprefix tailTrace_8140298
  have hstable : (prefixWord ++ tailWord_8140298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140298).length < 2 ^ (prefixWord ++ tailWord_8140298).sum := by decide
  have hdescent : baseEnd_8140298 < baseStart_8140298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140314 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_8140314 : Nat := 118140960795 + 8140314 * 2 ^ 59
def prefixEnd_8140314 : Nat := 4983230072969 + 3 ^ 40 * 8140314 * 2
def baseEnd_8140314 : Nat := 4179893760523769217738383

theorem tailTrace_8140314 : CollatzResearch.WordTrace tailWord_8140314 prefixEnd_8140314 4179893760523769217738383 := by
  unfold tailWord_8140314
  simp only [CollatzResearch.WordTrace]
  refine ⟨74225410757760026948114999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197934428687360071861639997 74225410757760026948114999)
  ·
    refine ⟨111338116136640040422172499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74225410757760026948114999 111338116136640040422172499)
    ·
      refine ⟨167007174204960060633258749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111338116136640040422172499 167007174204960060633258749)
      ·
        refine ⟨62627690326860022737472031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167007174204960060633258749 62627690326860022737472031)
        ·
          refine ⟨93941535490290034106208047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62627690326860022737472031 93941535490290034106208047)
          ·
            refine ⟨140912303235435051159312071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93941535490290034106208047 140912303235435051159312071)
            ·
              refine ⟨211368454853152576738968107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140912303235435051159312071 211368454853152576738968107)
              ·
                refine ⟨317052682279728865108452161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211368454853152576738968107 317052682279728865108452161)
                ·
                  refine ⟨237789511709796648831339121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317052682279728865108452161 237789511709796648831339121)
                  ·
                    refine ⟨178342133782347486623504341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237789511709796648831339121 178342133782347486623504341)
                    ·
                      refine ⟨4179893760523769217738383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178342133782347486623504341 4179893760523769217738383)
                      ·
                        rfl

theorem cell23_8140314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_8140314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140314 prefixEnd_8140314 := by exact prefixLift 8140314
  have htrace : WordTrace (prefixWord ++ tailWord_8140314) baseStart_8140314 baseEnd_8140314 := by
    simpa [prefixWord, tailWord_8140314, baseEnd_8140314] using wordTrace_append hprefix tailTrace_8140314
  have hstable : (prefixWord ++ tailWord_8140314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140314).length < 2 ^ (prefixWord ++ tailWord_8140314).sum := by decide
  have hdescent : baseEnd_8140314 < baseStart_8140314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140328 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_8140328 : Nat := 118140960795 + 8140328 * 2 ^ 59
def prefixEnd_8140328 : Nat := 4983230072969 + 3 ^ 40 * 8140328 * 2
def baseEnd_8140328 : Nat := 4179900949252932162963319

theorem tailTrace_8140328 : CollatzResearch.WordTrace tailWord_8140328 prefixEnd_8140328 4179900949252932162963319 := by
  unfold tailWord_8140328
  simp only [CollatzResearch.WordTrace]
  refine ⟨148451076826494694091734819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197934769101992925455646425 148451076826494694091734819)
  ·
    refine ⟨222676615239742041137602229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148451076826494694091734819 222676615239742041137602229)
    ·
      refine ⟨20875932678725816356650209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222676615239742041137602229 20875932678725816356650209)
      ·
        refine ⟨15656949509044362267487657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20875932678725816356650209 15656949509044362267487657)
        ·
          refine ⟨11742712131783271700615743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15656949509044362267487657 11742712131783271700615743)
          ·
            refine ⟨17614068197674907550923615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742712131783271700615743 17614068197674907550923615)
            ·
              refine ⟨26421102296512361326385423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17614068197674907550923615 26421102296512361326385423)
              ·
                refine ⟨39631653444768541989578135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26421102296512361326385423 39631653444768541989578135)
                ·
                  refine ⟨59447480167152812984367203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39631653444768541989578135 59447480167152812984367203)
                  ·
                    refine ⟨89171220250729219476550805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59447480167152812984367203 89171220250729219476550805)
                    ·
                      refine ⟨4179900949252932162963319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89171220250729219476550805 4179900949252932162963319)
                      ·
                        rfl

theorem cell23_8140328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_8140328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140328 prefixEnd_8140328 := by exact prefixLift 8140328
  have htrace : WordTrace (prefixWord ++ tailWord_8140328) baseStart_8140328 baseEnd_8140328 := by
    simpa [prefixWord, tailWord_8140328, baseEnd_8140328] using wordTrace_append hprefix tailTrace_8140328
  have hstable : (prefixWord ++ tailWord_8140328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140328).length < 2 ^ (prefixWord ++ tailWord_8140328).sum := by decide
  have hdescent : baseEnd_8140328 < baseStart_8140328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140391 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_8140391 : Nat := 118140960795 + 8140391 * 2 ^ 59
def prefixEnd_8140391 : Nat := 4983230072969 + 3 ^ 40 * 8140391 * 2
def baseEnd_8140391 : Nat := 4179933298534165416475529

theorem tailTrace_8140391 : CollatzResearch.WordTrace tailWord_8140391 prefixEnd_8140391 4179933298534165416475529 := by
  unfold tailWord_8140391
  simp only [CollatzResearch.WordTrace]
  refine ⟨296904451451761149943013027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197936300967840766628675351 296904451451761149943013027)
  ·
    refine ⟨445356677177641724914519541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296904451451761149943013027 445356677177641724914519541)
    ·
      refine ⟨41752188485403911710736207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 445356677177641724914519541 41752188485403911710736207)
      ·
        refine ⟨62628282728105867566104311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41752188485403911710736207 62628282728105867566104311)
        ·
          refine ⟨93942424092158801349156467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62628282728105867566104311 93942424092158801349156467)
          ·
            refine ⟨140913636138238202023734701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93942424092158801349156467 140913636138238202023734701)
            ·
              refine ⟨52842613551839325758900513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140913636138238202023734701 52842613551839325758900513)
              ·
                refine ⟨39631960163879494319175385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52842613551839325758900513 39631960163879494319175385)
                ·
                  refine ⟨29723970122909620739381539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39631960163879494319175385 29723970122909620739381539)
                  ·
                    refine ⟨44585955184364431109072309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29723970122909620739381539 44585955184364431109072309)
                    ·
                      refine ⟨4179933298534165416475529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44585955184364431109072309 4179933298534165416475529)
                      ·
                        rfl

theorem cell23_8140391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_8140391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140391 prefixEnd_8140391 := by exact prefixLift 8140391
  have htrace : WordTrace (prefixWord ++ tailWord_8140391) baseStart_8140391 baseEnd_8140391 := by
    simpa [prefixWord, tailWord_8140391, baseEnd_8140391] using wordTrace_append hprefix tailTrace_8140391
  have hstable : (prefixWord ++ tailWord_8140391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140391).length < 2 ^ (prefixWord ++ tailWord_8140391).sum := by decide
  have hdescent : baseEnd_8140391 < baseStart_8140391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140392 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_8140392 : Nat := 118140960795 + 8140392 * 2 ^ 59
def prefixEnd_8140392 : Nat := 4983230072969 + 3 ^ 40 * 8140392 * 2
def baseEnd_8140392 : Nat := 4179933812014819912563025

theorem tailTrace_8140392 : CollatzResearch.WordTrace tailWord_8140392 prefixEnd_8140392 4179933812014819912563025 := by
  unfold tailWord_8140392
  simp only [CollatzResearch.WordTrace]
  refine ⟨148452243962378763556899715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197936325283171684742532953 148452243962378763556899715)
  ·
    refine ⟨222678365943568145335349573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148452243962378763556899715 222678365943568145335349573)
    ·
      refine ⟨41752193614419027250378045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222678365943568145335349573 41752193614419027250378045)
      ·
        refine ⟨15657072605407135218891767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41752193614419027250378045 15657072605407135218891767)
        ·
          refine ⟨23485608908110702828337651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15657072605407135218891767 23485608908110702828337651)
          ·
            refine ⟨35228413362166054242506477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23485608908110702828337651 35228413362166054242506477)
            ·
              refine ⟨13210655010812270340939929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35228413362166054242506477 13210655010812270340939929)
              ·
                refine ⟨9907991258109202755704947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13210655010812270340939929 9907991258109202755704947)
                ·
                  refine ⟨14861986887163804133557421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9907991258109202755704947 14861986887163804133557421)
                  ·
                    refine ⟨5573245082686426550084033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14861986887163804133557421 5573245082686426550084033)
                    ·
                      refine ⟨4179933812014819912563025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573245082686426550084033 4179933812014819912563025)
                      ·
                        rfl

theorem cell23_8140392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_8140392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140392 prefixEnd_8140392 := by exact prefixLift 8140392
  have htrace : WordTrace (prefixWord ++ tailWord_8140392) baseStart_8140392 baseEnd_8140392 := by
    simpa [prefixWord, tailWord_8140392, baseEnd_8140392] using wordTrace_append hprefix tailTrace_8140392
  have hstable : (prefixWord ++ tailWord_8140392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140392).length < 2 ^ (prefixWord ++ tailWord_8140392).sum := by decide
  have hdescent : baseEnd_8140392 < baseStart_8140392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140405 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_8140405 : Nat := 118140960795 + 8140405 * 2 ^ 59
def prefixEnd_8140405 : Nat := 4983230072969 + 3 ^ 40 * 8140405 * 2
def baseEnd_8140405 : Nat := 4179940487263328361700465

theorem tailTrace_8140405 : CollatzResearch.WordTrace tailWord_8140405 prefixEnd_8140405 4179940487263328361700465 := by
  unfold tailWord_8140405
  simp only [CollatzResearch.WordTrace]
  refine ⟨296904962073710430334022669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197936641382473620222681779 296904962073710430334022669)
  ·
    refine ⟨111339360777641411375258501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296904962073710430334022669 111339360777641411375258501)
    ·
      refine ⟨20876130145807764632860969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111339360777641411375258501 20876130145807764632860969)
      ·
        refine ⟨15657097609355823474645727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20876130145807764632860969 15657097609355823474645727)
        ·
          refine ⟨23485646414033735211968591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15657097609355823474645727 23485646414033735211968591)
          ·
            refine ⟨35228469621050602817952887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23485646414033735211968591 35228469621050602817952887)
            ·
              refine ⟨52842704431575904226929331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35228469621050602817952887 52842704431575904226929331)
              ·
                refine ⟨79264056647363856340393997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52842704431575904226929331 79264056647363856340393997)
                ·
                  refine ⟨29724021242761446127647749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79264056647363856340393997 29724021242761446127647749)
                  ·
                    refine ⟨5573253983017771148933953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29724021242761446127647749 5573253983017771148933953)
                    ·
                      refine ⟨4179940487263328361700465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573253983017771148933953 4179940487263328361700465)
                      ·
                        rfl

theorem cell23_8140405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_8140405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140405 prefixEnd_8140405 := by exact prefixLift 8140405
  have htrace : WordTrace (prefixWord ++ tailWord_8140405) baseStart_8140405 baseEnd_8140405 := by
    simpa [prefixWord, tailWord_8140405, baseEnd_8140405] using wordTrace_append hprefix tailTrace_8140405
  have hstable : (prefixWord ++ tailWord_8140405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140405).length < 2 ^ (prefixWord ++ tailWord_8140405).sum := by decide
  have hdescent : baseEnd_8140405 < baseStart_8140405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140428 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 5]
def baseStart_8140428 : Nat := 118140960795 + 8140428 * 2 ^ 59
def prefixEnd_8140428 : Nat := 4983230072969 + 3 ^ 40 * 8140428 * 2
def baseEnd_8140428 : Nat := 464439144146486863523651

theorem tailTrace_8140428 : CollatzResearch.WordTrace tailWord_8140428 prefixEnd_8140428 464439144146486863523651 := by
  unfold tailWord_8140428
  simp only [CollatzResearch.WordTrace]
  refine ⟨148452900476313552631054969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197937200635084736841406625 148452900476313552631054969)
  ·
    refine ⟨111339675357235164473291227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148452900476313552631054969 111339675357235164473291227)
    ·
      refine ⟨167009513035852746709936841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111339675357235164473291227 167009513035852746709936841)
      ·
        refine ⟨125257134776889560032452631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167009513035852746709936841 125257134776889560032452631)
        ·
          refine ⟨187885702165334340048678947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125257134776889560032452631 187885702165334340048678947)
          ·
            refine ⟨281828553248001510073018421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187885702165334340048678947 281828553248001510073018421)
            ·
              refine ⟨26421426867000141569345477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281828553248001510073018421 26421426867000141569345477)
              ·
                refine ⟨4954017537562526544252277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26421426867000141569345477 4954017537562526544252277)
                ·
                  refine ⟨464439144146486863523651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954017537562526544252277 464439144146486863523651)
                  ·
                    rfl

theorem cell23_8140428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_8140428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140428 prefixEnd_8140428 := by exact prefixLift 8140428
  have htrace : WordTrace (prefixWord ++ tailWord_8140428) baseStart_8140428 baseEnd_8140428 := by
    simpa [prefixWord, tailWord_8140428, baseEnd_8140428] using wordTrace_append hprefix tailTrace_8140428
  have hstable : (prefixWord ++ tailWord_8140428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140428).length < 2 ^ (prefixWord ++ tailWord_8140428).sum := by decide
  have hdescent : baseEnd_8140428 < baseStart_8140428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140522 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_8140522 : Nat := 118140960795 + 8140522 * 2 ^ 59
def prefixEnd_8140522 : Nat := 4983230072969 + 3 ^ 40 * 8140522 * 2
def baseEnd_8140522 : Nat := 1393333521499968134645809

theorem tailTrace_8140522 : CollatzResearch.WordTrace tailWord_8140522 prefixEnd_8140522 1393333521499968134645809 := by
  unfold tailWord_8140522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74227307353571639829007955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197939486276191039544021213 74227307353571639829007955)
  ·
    refine ⟨111340961030357459743511933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74227307353571639829007955 111340961030357459743511933)
    ·
      refine ⟨41752860386384047403816975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111340961030357459743511933 41752860386384047403816975)
      ·
        refine ⟨62629290579576071105725463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41752860386384047403816975 62629290579576071105725463)
        ·
          refine ⟨93943935869364106658588195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62629290579576071105725463 93943935869364106658588195)
          ·
            refine ⟨140915903804046159987882293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93943935869364106658588195 140915903804046159987882293)
            ·
              refine ⟨13210865981629327498863965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140915903804046159987882293 13210865981629327498863965)
              ·
                refine ⟨4954074743110997812073987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13210865981629327498863965 4954074743110997812073987)
                ·
                  refine ⟨7431112114666496718110981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954074743110997812073987 7431112114666496718110981)
                  ·
                    refine ⟨1393333521499968134645809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431112114666496718110981 1393333521499968134645809)
                    ·
                      rfl

theorem cell23_8140522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_8140522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140522 prefixEnd_8140522 := by exact prefixLift 8140522
  have htrace : WordTrace (prefixWord ++ tailWord_8140522) baseStart_8140522 baseEnd_8140522 := by
    simpa [prefixWord, tailWord_8140522, baseEnd_8140522] using wordTrace_append hprefix tailTrace_8140522
  have hstable : (prefixWord ++ tailWord_8140522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140522).length < 2 ^ (prefixWord ++ tailWord_8140522).sum := by decide
  have hdescent : baseEnd_8140522 < baseStart_8140522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140565 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_8140565 : Nat := 118140960795 + 8140565 * 2 ^ 59
def prefixEnd_8140565 : Nat := 4983230072969 + 3 ^ 40 * 8140565 * 2
def baseEnd_8140565 : Nat := 1393340881389349245233243

theorem tailTrace_8140565 : CollatzResearch.WordTrace tailWord_8140565 prefixEnd_8140565 1393340881389349245233243 := by
  unfold tailWord_8140565
  simp only [CollatzResearch.WordTrace]
  refine ⟨296910797753130777659847149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197940531835420518439898099 296910797753130777659847149)
  ·
    refine ⟨111341549157424041622442681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296910797753130777659847149 111341549157424041622442681)
    ·
      refine ⟨83506161868068031216832011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111341549157424041622442681 83506161868068031216832011)
      ·
        refine ⟨125259242802102046825248017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83506161868068031216832011 125259242802102046825248017)
        ·
          refine ⟨93944432101576535118936013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125259242802102046825248017 93944432101576535118936013)
          ·
            refine ⟨35229162038091200669601005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93944432101576535118936013 35229162038091200669601005)
            ·
              refine ⟨13210935764284200251100377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35229162038091200669601005 13210935764284200251100377)
              ·
                refine ⟨9908201823213150188325283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13210935764284200251100377 9908201823213150188325283)
                ·
                  refine ⟨14862302734819725282487925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908201823213150188325283 14862302734819725282487925)
                  ·
                    refine ⟨1393340881389349245233243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14862302734819725282487925 1393340881389349245233243)
                    ·
                      rfl

theorem cell23_8140565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_8140565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140565 prefixEnd_8140565 := by exact prefixLift 8140565
  have htrace : WordTrace (prefixWord ++ tailWord_8140565) baseStart_8140565 baseEnd_8140565 := by
    simpa [prefixWord, tailWord_8140565, baseEnd_8140565] using wordTrace_append hprefix tailTrace_8140565
  have hstable : (prefixWord ++ tailWord_8140565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140565).length < 2 ^ (prefixWord ++ tailWord_8140565).sum := by decide
  have hdescent : baseEnd_8140565 < baseStart_8140565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140572 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_8140572 : Nat := 118140960795 + 8140572 * 2 ^ 59
def prefixEnd_8140572 : Nat := 4983230072969 + 3 ^ 40 * 8140572 * 2
def baseEnd_8140572 : Nat := 4180026238532629208312197

theorem tailTrace_8140572 : CollatzResearch.WordTrace tailWord_8140572 prefixEnd_8140572 4180026238532629208312197 := by
  unfold tailWord_8140572
  simp only [CollatzResearch.WordTrace]
  refine ⟨148455526532052708927675985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197940702042736945236901313 148455526532052708927675985)
  ·
    refine ⟨111341644899039531695756989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148455526532052708927675985 111341644899039531695756989)
    ·
      refine ⟨41753116837139824385908871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111341644899039531695756989 41753116837139824385908871)
      ·
        refine ⟨62629675255709736578863307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41753116837139824385908871 62629675255709736578863307)
        ·
          refine ⟨93944512883564604868294961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62629675255709736578863307 93944512883564604868294961)
          ·
            refine ⟨70458384662673453651221221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93944512883564604868294961 70458384662673453651221221)
            ·
              refine ⟨13210947124251272559603979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70458384662673453651221221 13210947124251272559603979)
              ·
                refine ⟨19816420686376908839405969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13210947124251272559603979 19816420686376908839405969)
                ·
                  refine ⟨14862315514782681629554477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19816420686376908839405969 14862315514782681629554477)
                  ·
                    refine ⟨5573368318043505611082929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14862315514782681629554477 5573368318043505611082929)
                    ·
                      refine ⟨4180026238532629208312197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573368318043505611082929 4180026238532629208312197)
                      ·
                        rfl

theorem cell23_8140572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_8140572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140572 prefixEnd_8140572 := by exact prefixLift 8140572
  have htrace : WordTrace (prefixWord ++ tailWord_8140572) baseStart_8140572 baseEnd_8140572 := by
    simpa [prefixWord, tailWord_8140572, baseEnd_8140572] using wordTrace_append hprefix tailTrace_8140572
  have hstable : (prefixWord ++ tailWord_8140572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140572).length < 2 ^ (prefixWord ++ tailWord_8140572).sum := by decide
  have hdescent : baseEnd_8140572 < baseStart_8140572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140596 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_8140596 : Nat := 118140960795 + 8140596 * 2 ^ 59
def prefixEnd_8140596 : Nat := 4983230072969 + 3 ^ 40 * 8140596 * 2
def baseEnd_8140596 : Nat := 4180038562068337114412087

theorem tailTrace_8140596 : CollatzResearch.WordTrace tailWord_8140596 prefixEnd_8140596 4180038562068337114412087 := by
  unfold tailWord_8140596
  simp only [CollatzResearch.WordTrace]
  refine ⟨148455964208009234977112821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197941285610678979969483761 148455964208009234977112821)
  ·
    refine ⟨13917746644500865779104327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148455964208009234977112821 13917746644500865779104327)
    ·
      refine ⟨20876619966751298668656491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13917746644500865779104327 20876619966751298668656491)
      ·
        refine ⟨31314929950126948002984737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20876619966751298668656491 31314929950126948002984737)
        ·
          refine ⟨23486197462595211002238553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31314929950126948002984737 23486197462595211002238553)
          ·
            refine ⟨17614648096946408251678915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23486197462595211002238553 17614648096946408251678915)
            ·
              refine ⟨26421972145419612377518373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17614648096946408251678915 26421972145419612377518373)
              ·
                refine ⟨4954119777266177320784695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26421972145419612377518373 4954119777266177320784695)
                ·
                  refine ⟨7431179665899265981177043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954119777266177320784695 7431179665899265981177043)
                  ·
                    refine ⟨11146769498848898971765565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431179665899265981177043 11146769498848898971765565)
                    ·
                      refine ⟨4180038562068337114412087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11146769498848898971765565 4180038562068337114412087)
                      ·
                        rfl

theorem cell23_8140596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_8140596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140596 prefixEnd_8140596 := by exact prefixLift 8140596
  have htrace : WordTrace (prefixWord ++ tailWord_8140596) baseStart_8140596 baseEnd_8140596 := by
    simpa [prefixWord, tailWord_8140596, baseEnd_8140596] using wordTrace_append hprefix tailTrace_8140596
  have hstable : (prefixWord ++ tailWord_8140596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140596).length < 2 ^ (prefixWord ++ tailWord_8140596).sum := by decide
  have hdescent : baseEnd_8140596 < baseStart_8140596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140625 : List Nat := [1, 2, 2, 1, 5, 2, 3, 7]
def baseStart_8140625 : Nat := 118140960795 + 8140625 * 2 ^ 59
def prefixEnd_8140625 : Nat := 4983230072969 + 3 ^ 40 * 8140625 * 2
def baseEnd_8140625 : Nat := 154816794555826574109239

theorem tailTrace_8140625 : CollatzResearch.WordTrace tailWord_8140625 prefixEnd_8140625 154816794555826574109239 := by
  unfold tailWord_8140625
  simp only [CollatzResearch.WordTrace]
  refine ⟨296912986132913407907031329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197941990755275605271354219 296912986132913407907031329)
  ·
    refine ⟨222684739599685055930273497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296912986132913407907031329 222684739599685055930273497)
    ·
      refine ⟨167013554699763791947705123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222684739599685055930273497 167013554699763791947705123)
      ·
        refine ⟨250520332049645687921557685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167013554699763791947705123 250520332049645687921557685)
        ·
          refine ⟨23486281129654283242646033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250520332049645687921557685 23486281129654283242646033)
          ·
            refine ⟨17614710847240712431984525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23486281129654283242646033 17614710847240712431984525)
            ·
              refine ⟨6605516567715267161994197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17614710847240712431984525 6605516567715267161994197)
              ·
                refine ⟨154816794555826574109239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6605516567715267161994197 154816794555826574109239)
                ·
                  rfl

theorem cell23_8140625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 7].length) (baseStart_8140625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140625 prefixEnd_8140625 := by exact prefixLift 8140625
  have htrace : WordTrace (prefixWord ++ tailWord_8140625) baseStart_8140625 baseEnd_8140625 := by
    simpa [prefixWord, tailWord_8140625, baseEnd_8140625] using wordTrace_append hprefix tailTrace_8140625
  have hstable : (prefixWord ++ tailWord_8140625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140625).length < 2 ^ (prefixWord ++ tailWord_8140625).sum := by decide
  have hdescent : baseEnd_8140625 < baseStart_8140625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140636 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_8140636 : Nat := 118140960795 + 8140636 * 2 ^ 59
def prefixEnd_8140636 : Nat := 4983230072969 + 3 ^ 40 * 8140636 * 2
def baseEnd_8140636 : Nat := 4180059101294516957911903

theorem tailTrace_8140636 : CollatzResearch.WordTrace tailWord_8140636 prefixEnd_8140636 4180059101294516957911903 := by
  unfold tailWord_8140636
  simp only [CollatzResearch.WordTrace]
  refine ⟨148456693667936778392840881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197942258223915704523787841 148456693667936778392840881)
  ·
    refine ⟨111342520250952583794630661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148456693667936778392840881 111342520250952583794630661)
    ·
      refine ⟨20876722547053609461493249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111342520250952583794630661 20876722547053609461493249)
      ·
        refine ⟨15657541910290207096119937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20876722547053609461493249 15657541910290207096119937)
        ·
          refine ⟨11743156432717655322089953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15657541910290207096119937 11743156432717655322089953)
          ·
            refine ⟨8807367324538241491567465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11743156432717655322089953 8807367324538241491567465)
            ·
              refine ⟨6605525493403681118675599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807367324538241491567465 6605525493403681118675599)
              ·
                refine ⟨9908288240105521678013399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605525493403681118675599 9908288240105521678013399)
                ·
                  refine ⟨14862432360158282517020099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908288240105521678013399 14862432360158282517020099)
                  ·
                    refine ⟨22293648540237423775530149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14862432360158282517020099 22293648540237423775530149)
                    ·
                      refine ⟨4180059101294516957911903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22293648540237423775530149 4180059101294516957911903)
                      ·
                        rfl

theorem cell23_8140636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_8140636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140636 prefixEnd_8140636 := by exact prefixLift 8140636
  have htrace : WordTrace (prefixWord ++ tailWord_8140636) baseStart_8140636 baseEnd_8140636 := by
    simpa [prefixWord, tailWord_8140636, baseEnd_8140636] using wordTrace_append hprefix tailTrace_8140636
  have hstable : (prefixWord ++ tailWord_8140636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140636).length < 2 ^ (prefixWord ++ tailWord_8140636).sum := by decide
  have hdescent : baseEnd_8140636 < baseStart_8140636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140639 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 1, 2, 3]
def baseStart_8140639 : Nat := 118140960795 + 8140639 * 2 ^ 59
def prefixEnd_8140639 : Nat := 4983230072969 + 3 ^ 40 * 8140639 * 2
def baseEnd_8140639 : Nat := 4180060641736480446174389

theorem tailTrace_8140639 : CollatzResearch.WordTrace tailWord_8140639 prefixEnd_8140639 4180060641736480446174389 := by
  unfold tailWord_8140639
  simp only [CollatzResearch.WordTrace]
  refine ⟨296913496754862688298040971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197942331169908458865360647 296913496754862688298040971)
  ·
    refine ⟨445370245132294032447061457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296913496754862688298040971 445370245132294032447061457)
    ·
      refine ⟨334027683849220524335296093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445370245132294032447061457 334027683849220524335296093)
      ·
        refine ⟨125260381443457696625736035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334027683849220524335296093 125260381443457696625736035)
        ·
          refine ⟨187890572165186544938604053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125260381443457696625736035 187890572165186544938604053)
          ·
            refine ⟨8807370570243119293997065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187890572165186544938604053 8807370570243119293997065)
            ·
              refine ⟨6605527927682339470497799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807370570243119293997065 6605527927682339470497799)
              ·
                refine ⟨9908291891523509205746699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605527927682339470497799 9908291891523509205746699)
                ·
                  refine ⟨14862437837285263808620049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908291891523509205746699 14862437837285263808620049)
                  ·
                    refine ⟨11146828377963947856465037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14862437837285263808620049 11146828377963947856465037)
                    ·
                      refine ⟨4180060641736480446174389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11146828377963947856465037 4180060641736480446174389)
                      ·
                        rfl

theorem cell23_8140639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_8140639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140639 prefixEnd_8140639 := by exact prefixLift 8140639
  have htrace : WordTrace (prefixWord ++ tailWord_8140639) baseStart_8140639 baseEnd_8140639 := by
    simpa [prefixWord, tailWord_8140639, baseEnd_8140639] using wordTrace_append hprefix tailTrace_8140639
  have hstable : (prefixWord ++ tailWord_8140639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140639).length < 2 ^ (prefixWord ++ tailWord_8140639).sum := by decide
  have hdescent : baseEnd_8140639 < baseStart_8140639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140652 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_8140652 : Nat := 118140960795 + 8140652 * 2 ^ 59
def prefixEnd_8140652 : Nat := 4983230072969 + 3 ^ 40 * 8140652 * 2
def baseEnd_8140652 : Nat := 4180067316984988895311829

theorem tailTrace_8140652 : CollatzResearch.WordTrace tailWord_8140652 prefixEnd_8140652 4180067316984988895311829 := by
  unfold tailWord_8140652
  simp only [CollatzResearch.WordTrace]
  refine ⟨148456985451907795759132105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197942647269210394345509473 148456985451907795759132105)
  ·
    refine ⟨111342739088930846819349079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148456985451907795759132105 111342739088930846819349079)
    ·
      refine ⟨167014108633396270229023619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111342739088930846819349079 167014108633396270229023619)
      ·
        refine ⟨250521162950094405343535429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167014108633396270229023619 250521162950094405343535429)
        ·
          refine ⟨46972718053142701001912893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250521162950094405343535429 46972718053142701001912893)
          ·
            refine ⟨17614769269928512875717335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46972718053142701001912893 17614769269928512875717335)
            ·
              refine ⟨26422153904892769313576003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17614769269928512875717335 26422153904892769313576003)
              ·
                refine ⟨39633230857339153970364005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26422153904892769313576003 39633230857339153970364005)
                ·
                  refine ⟨7431230785751091369443251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39633230857339153970364005 7431230785751091369443251)
                  ·
                    refine ⟨11146846178626637054164877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431230785751091369443251 11146846178626637054164877)
                    ·
                      refine ⟨4180067316984988895311829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11146846178626637054164877 4180067316984988895311829)
                      ·
                        rfl

theorem cell23_8140652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_8140652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140652 prefixEnd_8140652 := by exact prefixLift 8140652
  have htrace : WordTrace (prefixWord ++ tailWord_8140652) baseStart_8140652 baseEnd_8140652 := by
    simpa [prefixWord, tailWord_8140652, baseEnd_8140652] using wordTrace_append hprefix tailTrace_8140652
  have hstable : (prefixWord ++ tailWord_8140652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140652).length < 2 ^ (prefixWord ++ tailWord_8140652).sum := by decide
  have hdescent : baseEnd_8140652 < baseStart_8140652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140688 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_8140688 : Nat := 118140960795 + 8140688 * 2 ^ 59
def prefixEnd_8140688 : Nat := 4983230072969 + 3 ^ 40 * 8140688 * 2
def baseEnd_8140688 : Nat := 4180085802288550754461663

theorem tailTrace_8140688 : CollatzResearch.WordTrace tailWord_8140688 prefixEnd_8140688 4180085802288550754461663 := by
  unfold tailWord_8140688
  simp only [CollatzResearch.WordTrace]
  refine ⟨148457641965842584833287359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197943522621123446444383145 148457641965842584833287359)
  ·
    refine ⟨222686462948763877249931039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148457641965842584833287359 222686462948763877249931039)
    ·
      refine ⟨334029694423145815874896559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222686462948763877249931039 334029694423145815874896559)
      ·
        refine ⟨501044541634718723812344839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334029694423145815874896559 501044541634718723812344839)
        ·
          refine ⟨751566812452078085718517259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501044541634718723812344839 751566812452078085718517259)
          ·
            refine ⟨1127350218678117128577775889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751566812452078085718517259 1127350218678117128577775889)
            ·
              refine ⟨845512664008587846433331917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127350218678117128577775889 845512664008587846433331917)
              ·
                refine ⟨317067249003220442412499469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845512664008587846433331917 317067249003220442412499469)
                ·
                  refine ⟨118900218376207665904687301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317067249003220442412499469 118900218376207665904687301)
                  ·
                    refine ⟨22293790945538937357128869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118900218376207665904687301 22293790945538937357128869)
                    ·
                      refine ⟨4180085802288550754461663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22293790945538937357128869 4180085802288550754461663)
                      ·
                        rfl

theorem cell23_8140688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_8140688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140688 prefixEnd_8140688 := by exact prefixLift 8140688
  have htrace : WordTrace (prefixWord ++ tailWord_8140688) baseStart_8140688 baseEnd_8140688 := by
    simpa [prefixWord, tailWord_8140688, baseEnd_8140688] using wordTrace_append hprefix tailTrace_8140688
  have hstable : (prefixWord ++ tailWord_8140688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140688).length < 2 ^ (prefixWord ++ tailWord_8140688).sum := by decide
  have hdescent : baseEnd_8140688 < baseStart_8140688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140695 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_8140695 : Nat := 118140960795 + 8140695 * 2 ^ 59
def prefixEnd_8140695 : Nat := 4983230072969 + 3 ^ 40 * 8140695 * 2
def baseEnd_8140695 : Nat := 4180089396653132227074131

theorem tailTrace_8140695 : CollatzResearch.WordTrace tailWord_8140695 prefixEnd_8140695 4180089396653132227074131 := by
  unfold tailWord_8140695
  simp only [CollatzResearch.WordTrace]
  refine ⟨296915539242659809862079539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197943692828439873241386359 296915539242659809862079539)
  ·
    refine ⟨445373308863989714793119309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296915539242659809862079539 445373308863989714793119309)
    ·
      refine ⟨167014990823996143047419741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445373308863989714793119309 167014990823996143047419741)
      ·
        refine ⟨62630621558998553642782403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167014990823996143047419741 62630621558998553642782403)
        ·
          refine ⟨93945932338497830464173605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62630621558998553642782403 93945932338497830464173605)
          ·
            refine ⟨17614862313468343212032551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93945932338497830464173605 17614862313468343212032551)
            ·
              refine ⟨26422293470202514818048827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17614862313468343212032551 26422293470202514818048827)
              ·
                refine ⟨39633440205303772227073241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26422293470202514818048827 39633440205303772227073241)
                ·
                  refine ⟨29725080153977829170304931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39633440205303772227073241 29725080153977829170304931)
                  ·
                    refine ⟨44587620230966743755457397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29725080153977829170304931 44587620230966743755457397)
                    ·
                      refine ⟨4180089396653132227074131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44587620230966743755457397 4180089396653132227074131)
                      ·
                        rfl

theorem cell23_8140695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_8140695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140695 prefixEnd_8140695 := by exact prefixLift 8140695
  have htrace : WordTrace (prefixWord ++ tailWord_8140695) baseStart_8140695 baseEnd_8140695 := by
    simpa [prefixWord, tailWord_8140695, baseEnd_8140695] using wordTrace_append hprefix tailTrace_8140695
  have hstable : (prefixWord ++ tailWord_8140695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140695).length < 2 ^ (prefixWord ++ tailWord_8140695).sum := by decide
  have hdescent : baseEnd_8140695 < baseStart_8140695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140849 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_8140849 : Nat := 118140960795 + 8140849 * 2 ^ 59
def prefixEnd_8140849 : Nat := 4983230072969 + 3 ^ 40 * 8140849 * 2
def baseEnd_8140849 : Nat := 4180168472673924624548423

theorem tailTrace_8140849 : CollatzResearch.WordTrace tailWord_8140849 prefixEnd_8140849 4180168472673924624548423 := by
  unfold tailWord_8140849
  simp only [CollatzResearch.WordTrace]
  refine ⟨296921156084101894163185601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197947437389401262775457067 296921156084101894163185601)
  ·
    refine ⟨222690867063076420622389201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296921156084101894163185601 222690867063076420622389201)
    ·
      refine ⟨167018150297307315466791901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222690867063076420622389201 167018150297307315466791901)
      ·
        refine ⟨62631806361490243300046963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167018150297307315466791901 62631806361490243300046963)
        ·
          refine ⟨93947709542235364950070445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62631806361490243300046963 93947709542235364950070445)
          ·
            refine ⟨35230391078338261856276417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93947709542235364950070445 35230391078338261856276417)
            ·
              refine ⟨26422793308753696392207313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35230391078338261856276417 26422793308753696392207313)
              ·
                refine ⟨19817094981565272294155485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26422793308753696392207313 19817094981565272294155485)
                ·
                  refine ⟨7431410618086977110308307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19817094981565272294155485 7431410618086977110308307)
                  ·
                    refine ⟨11147115927130465665462461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431410618086977110308307 11147115927130465665462461)
                    ·
                      refine ⟨4180168472673924624548423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147115927130465665462461 4180168472673924624548423)
                      ·
                        rfl

theorem cell23_8140849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_8140849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140849 prefixEnd_8140849 := by exact prefixLift 8140849
  have htrace : WordTrace (prefixWord ++ tailWord_8140849) baseStart_8140849 baseEnd_8140849 := by
    simpa [prefixWord, tailWord_8140849, baseEnd_8140849] using wordTrace_append hprefix tailTrace_8140849
  have hstable : (prefixWord ++ tailWord_8140849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140849).length < 2 ^ (prefixWord ++ tailWord_8140849).sum := by decide
  have hdescent : baseEnd_8140849 < baseStart_8140849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140875 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5]
def baseStart_8140875 : Nat := 118140960795 + 8140875 * 2 ^ 59
def prefixEnd_8140875 : Nat := 4983230072969 + 3 ^ 40 * 8140875 * 2
def baseEnd_8140875 : Nat := 4180181823170941522823303

theorem tailTrace_8140875 : CollatzResearch.WordTrace tailWord_8140875 prefixEnd_8140875 4180181823170941522823303 := by
  unfold tailWord_8140875
  simp only [CollatzResearch.WordTrace]
  refine ⟨296922104382007700603632079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197948069588005133735754719 296922104382007700603632079)
  ·
    refine ⟨445383156573011550905448119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296922104382007700603632079 445383156573011550905448119)
    ·
      refine ⟨668074734859517326358172179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445383156573011550905448119 668074734859517326358172179)
      ·
        refine ⟨1002112102289275989537258269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668074734859517326358172179 1002112102289275989537258269)
        ·
          refine ⟨375792038358478496076471851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002112102289275989537258269 375792038358478496076471851)
          ·
            refine ⟨563688057537717744114707777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375792038358478496076471851 563688057537717744114707777)
            ·
              refine ⟨422766043153288308086030833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563688057537717744114707777 422766043153288308086030833)
              ·
                refine ⟨317074532364966231064523125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422766043153288308086030833 317074532364966231064523125)
                ·
                  refine ⟨29725737409215584162299043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317074532364966231064523125 29725737409215584162299043)
                  ·
                    refine ⟨44588606113823376243448565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29725737409215584162299043 44588606113823376243448565)
                    ·
                      refine ⟨4180181823170941522823303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44588606113823376243448565 4180181823170941522823303)
                      ·
                        rfl

theorem cell23_8140875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_8140875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140875 prefixEnd_8140875 := by exact prefixLift 8140875
  have htrace : WordTrace (prefixWord ++ tailWord_8140875) baseStart_8140875 baseEnd_8140875 := by
    simpa [prefixWord, tailWord_8140875, baseEnd_8140875] using wordTrace_append hprefix tailTrace_8140875
  have hstable : (prefixWord ++ tailWord_8140875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140875).length < 2 ^ (prefixWord ++ tailWord_8140875).sum := by decide
  have hdescent : baseEnd_8140875 < baseStart_8140875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140909 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_8140909 : Nat := 118140960795 + 8140909 * 2 ^ 59
def prefixEnd_8140909 : Nat := 4983230072969 + 3 ^ 40 * 8140909 * 2
def baseEnd_8140909 : Nat := 4180199281513194389798147

theorem tailTrace_8140909 : CollatzResearch.WordTrace tailWord_8140909 prefixEnd_8140909 4180199281513194389798147 := by
  unfold tailWord_8140909
  simp only [CollatzResearch.WordTrace]
  refine ⟨296923344463884524410369781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197948896309256349606913187 296923344463884524410369781)
  ·
    refine ⟨27836563543489174163472167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296923344463884524410369781 27836563543489174163472167)
    ·
      refine ⟨41754845315233761245208251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27836563543489174163472167 41754845315233761245208251)
      ·
        refine ⟨62632267972850641867812377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41754845315233761245208251 62632267972850641867812377)
        ·
          refine ⟨46974200979637981400859283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62632267972850641867812377 46974200979637981400859283)
          ·
            refine ⟨70461301469456972101288925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46974200979637981400859283 70461301469456972101288925)
            ·
              refine ⟨26422988051046364537983347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70461301469456972101288925 26422988051046364537983347)
              ·
                refine ⟨39634482076569546806975021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26422988051046364537983347 39634482076569546806975021)
                ·
                  refine ⟨14862930778713580052615633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39634482076569546806975021 14862930778713580052615633)
                  ·
                    refine ⟨11147198084035185039461725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14862930778713580052615633 11147198084035185039461725)
                    ·
                      refine ⟨4180199281513194389798147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147198084035185039461725 4180199281513194389798147)
                      ·
                        rfl

theorem cell23_8140909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_8140909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140909 prefixEnd_8140909 := by exact prefixLift 8140909
  have htrace : WordTrace (prefixWord ++ tailWord_8140909) baseStart_8140909 baseEnd_8140909 := by
    simpa [prefixWord, tailWord_8140909, baseEnd_8140909] using wordTrace_append hprefix tailTrace_8140909
  have hstable : (prefixWord ++ tailWord_8140909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140909).length < 2 ^ (prefixWord ++ tailWord_8140909).sum := by decide
  have hdescent : baseEnd_8140909 < baseStart_8140909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140949 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_8140949 : Nat := 118140960795 + 8140949 * 2 ^ 59
def prefixEnd_8140949 : Nat := 4983230072969 + 3 ^ 40 * 8140949 * 2
def baseEnd_8140949 : Nat := 4180219820739374233297963

theorem tailTrace_8140949 : CollatzResearch.WordTrace tailWord_8140949 prefixEnd_8140949 4180219820739374233297963 := by
  unfold tailWord_8140949
  simp only [CollatzResearch.WordTrace]
  refine ⟨296924803383739611241825901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197949868922493074161217267 296924803383739611241825901)
  ·
    refine ⟨111346801268902354215684713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296924803383739611241825901 111346801268902354215684713)
    ·
      refine ⟨83510100951676765661763535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111346801268902354215684713 83510100951676765661763535)
      ·
        refine ⟨125265151427515148492645303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83510100951676765661763535 125265151427515148492645303)
        ·
          refine ⟨187897727141272722738967955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125265151427515148492645303 187897727141272722738967955)
          ·
            refine ⟨281846590711909084108451933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187897727141272722738967955 281846590711909084108451933)
            ·
              refine ⟨105692471516965906540669475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281846590711909084108451933 105692471516965906540669475)
              ·
                refine ⟨158538707275448859811004213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105692471516965906540669475 158538707275448859811004213)
                ·
                  refine ⟨14863003807073330607281645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158538707275448859811004213 14863003807073330607281645)
                  ·
                    refine ⟨5573626427652498977730617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14863003807073330607281645 5573626427652498977730617)
                    ·
                      refine ⟨4180219820739374233297963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573626427652498977730617 4180219820739374233297963)
                      ·
                        rfl

theorem cell23_8140949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_8140949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140949 prefixEnd_8140949 := by exact prefixLift 8140949
  have htrace : WordTrace (prefixWord ++ tailWord_8140949) baseStart_8140949 baseEnd_8140949 := by
    simpa [prefixWord, tailWord_8140949, baseEnd_8140949] using wordTrace_append hprefix tailTrace_8140949
  have hstable : (prefixWord ++ tailWord_8140949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140949).length < 2 ^ (prefixWord ++ tailWord_8140949).sum := by decide
  have hdescent : baseEnd_8140949 < baseStart_8140949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140956 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_8140956 : Nat := 118140960795 + 8140956 * 2 ^ 59
def prefixEnd_8140956 : Nat := 4983230072969 + 3 ^ 40 * 8140956 * 2
def baseEnd_8140956 : Nat := 4180223415103955705910431

theorem tailTrace_8140956 : CollatzResearch.WordTrace tailWord_8140956 prefixEnd_8140956 4180223415103955705910431 := by
  unfold tailWord_8140956
  simp only [CollatzResearch.WordTrace]
  refine ⟨148462529347357125718665361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197950039129809500958220481 148462529347357125718665361)
  ·
    refine ⟨111346897010517844288999021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148462529347357125718665361 111346897010517844288999021)
    ·
      refine ⟨41755086378944191608374633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111346897010517844288999021 41755086378944191608374633)
      ·
        refine ⟨31316314784208143706280975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41755086378944191608374633 31316314784208143706280975)
        ·
          refine ⟨46974472176312215559421463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31316314784208143706280975 46974472176312215559421463)
          ·
            refine ⟨70461708264468323339132195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46974472176312215559421463 70461708264468323339132195)
            ·
              refine ⟨105692562396702485008698293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70461708264468323339132195 105692562396702485008698293)
              ·
                refine ⟨9908677724690857969565465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105692562396702485008698293 9908677724690857969565465)
                ·
                  refine ⟨7431508293518143477174099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9908677724690857969565465 7431508293518143477174099)
                  ·
                    refine ⟨11147262440277215215761149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431508293518143477174099 11147262440277215215761149)
                    ·
                      refine ⟨4180223415103955705910431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147262440277215215761149 4180223415103955705910431)
                      ·
                        rfl

theorem cell23_8140956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_8140956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140956 prefixEnd_8140956 := by exact prefixLift 8140956
  have htrace : WordTrace (prefixWord ++ tailWord_8140956) baseStart_8140956 baseEnd_8140956 := by
    simpa [prefixWord, tailWord_8140956, baseEnd_8140956] using wordTrace_append hprefix tailTrace_8140956
  have hstable : (prefixWord ++ tailWord_8140956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140956).length < 2 ^ (prefixWord ++ tailWord_8140956).sum := by decide
  have hdescent : baseEnd_8140956 < baseStart_8140956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140974 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_8140974 : Nat := 118140960795 + 8140974 * 2 ^ 59
def prefixEnd_8140974 : Nat := 4983230072969 + 3 ^ 40 * 8140974 * 2
def baseEnd_8140974 : Nat := 4180232657755736635485349

theorem tailTrace_8140974 : CollatzResearch.WordTrace tailWord_8140974 prefixEnd_8140974 4180232657755736635485349 := by
  unfold tailWord_8140974
  simp only [CollatzResearch.WordTrace]
  refine ⟨37115714401081130063935747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197950476805766027007657317 37115714401081130063935747)
  ·
    refine ⟨55673571601621695095903621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37115714401081130063935747 55673571601621695095903621)
    ·
      refine ⟨10438794675304067830481929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55673571601621695095903621 10438794675304067830481929)
      ·
        refine ⟨7829096006478050872861447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10438794675304067830481929 7829096006478050872861447)
        ·
          refine ⟨11743644009717076309292171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829096006478050872861447 11743644009717076309292171)
          ·
            refine ⟨17615466014575614463938257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11743644009717076309292171 17615466014575614463938257)
            ·
              refine ⟨13211599510931710847953693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17615466014575614463938257 13211599510931710847953693)
              ·
                refine ⟨4954349816599391567982635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13211599510931710847953693 4954349816599391567982635)
                ·
                  refine ⟨7431524724899087351973953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954349816599391567982635 7431524724899087351973953)
                  ·
                    refine ⟨5573643543674315513980465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7431524724899087351973953 5573643543674315513980465)
                    ·
                      refine ⟨4180232657755736635485349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573643543674315513980465 4180232657755736635485349)
                      ·
                        rfl

theorem cell23_8140974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_8140974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140974 prefixEnd_8140974 := by exact prefixLift 8140974
  have htrace : WordTrace (prefixWord ++ tailWord_8140974) baseStart_8140974 baseEnd_8140974 := by
    simpa [prefixWord, tailWord_8140974, baseEnd_8140974] using wordTrace_append hprefix tailTrace_8140974
  have hstable : (prefixWord ++ tailWord_8140974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140974).length < 2 ^ (prefixWord ++ tailWord_8140974).sum := by decide
  have hdescent : baseEnd_8140974 < baseStart_8140974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140983 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 1, 3, 2]
def baseStart_8140983 : Nat := 118140960795 + 8140983 * 2 ^ 59
def prefixEnd_8140983 : Nat := 4983230072969 + 3 ^ 40 * 8140983 * 2
def baseEnd_8140983 : Nat := 4180237279081627100272807

theorem tailTrace_8140983 : CollatzResearch.WordTrace tailWord_8140983 prefixEnd_8140983 4180237279081627100272807 := by
  unfold tailWord_8140983
  simp only [CollatzResearch.WordTrace]
  refine ⟨296926043465616435048563603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197950695643744290032375735 296926043465616435048563603)
  ·
    refine ⟨445389065198424652572845405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296926043465616435048563603 445389065198424652572845405)
    ·
      refine ⟨167020899449409244714817027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445389065198424652572845405 167020899449409244714817027)
      ·
        refine ⟨250531349174113867072225541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167020899449409244714817027 250531349174113867072225541)
        ·
          refine ⟨46974627970146350076042289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250531349174113867072225541 46974627970146350076042289)
          ·
            refine ⟨35230970977609762557031717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46974627970146350076042289 35230970977609762557031717)
            ·
              refine ⟨6605807058301830479443447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35230970977609762557031717 6605807058301830479443447)
              ·
                refine ⟨9908710587452745719165171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605807058301830479443447 9908710587452745719165171)
                ·
                  refine ⟨14863065881179118578747757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908710587452745719165171 14863065881179118578747757)
                  ·
                    refine ⟨5573649705442169467030409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14863065881179118578747757 5573649705442169467030409)
                    ·
                      refine ⟨4180237279081627100272807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573649705442169467030409 4180237279081627100272807)
                      ·
                        rfl

theorem cell23_8140983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_8140983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140983 prefixEnd_8140983 := by exact prefixLift 8140983
  have htrace : WordTrace (prefixWord ++ tailWord_8140983) baseStart_8140983 baseEnd_8140983 := by
    simpa [prefixWord, tailWord_8140983, baseEnd_8140983] using wordTrace_append hprefix tailTrace_8140983
  have hstable : (prefixWord ++ tailWord_8140983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140983).length < 2 ^ (prefixWord ++ tailWord_8140983).sum := by decide
  have hdescent : baseEnd_8140983 < baseStart_8140983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8140990 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_8140990 : Nat := 118140960795 + 8140990 * 2 ^ 59
def prefixEnd_8140990 : Nat := 4983230072969 + 3 ^ 40 * 8140990 * 2
def baseEnd_8140990 : Nat := 4180240873446208572885275

theorem tailTrace_8140990 : CollatzResearch.WordTrace tailWord_8140990 prefixEnd_8140990 4180240873446208572885275 := by
  unfold tailWord_8140990
  simp only [CollatzResearch.WordTrace]
  refine ⟨37115787347073884405508553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197950865851060716829378949 37115787347073884405508553)
  ·
    refine ⟨27836840510305413304131415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37115787347073884405508553 27836840510305413304131415)
    ·
      refine ⟨41755260765458119956197123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27836840510305413304131415 41755260765458119956197123)
      ·
        refine ⟨62632891148187179934295685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41755260765458119956197123 62632891148187179934295685)
        ·
          refine ⟨11743667090285096237680441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62632891148187179934295685 11743667090285096237680441)
          ·
            refine ⟨8807750317713822178260331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11743667090285096237680441 8807750317713822178260331)
            ·
              refine ⟨13211625476570733267390497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807750317713822178260331 13211625476570733267390497)
              ·
                refine ⟨9908719107428049950542873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13211625476570733267390497 9908719107428049950542873)
                ·
                  refine ⟨7431539330571037462907155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9908719107428049950542873 7431539330571037462907155)
                  ·
                    refine ⟨11147308995856556194360733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431539330571037462907155 11147308995856556194360733)
                    ·
                      refine ⟨4180240873446208572885275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147308995856556194360733 4180240873446208572885275)
                      ·
                        rfl

theorem cell23_8140990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_8140990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8140990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8140990 prefixEnd_8140990 := by exact prefixLift 8140990
  have htrace : WordTrace (prefixWord ++ tailWord_8140990) baseStart_8140990 baseEnd_8140990 := by
    simpa [prefixWord, tailWord_8140990, baseEnd_8140990] using wordTrace_append hprefix tailTrace_8140990
  have hstable : (prefixWord ++ tailWord_8140990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8140990).length < 2 ^ (prefixWord ++ tailWord_8140990).sum := by decide
  have hdescent : baseEnd_8140990 < baseStart_8140990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8140990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141089 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_8141089 : Nat := 118140960795 + 8141089 * 2 ^ 59
def prefixEnd_8141089 : Nat := 4983230072969 + 3 ^ 40 * 8141089 * 2
def baseEnd_8141089 : Nat := 4180291708031003685547319

theorem tailTrace_8141089 : CollatzResearch.WordTrace tailWord_8141089 prefixEnd_8141089 4180291708031003685547319 := by
  unfold tailWord_8141089
  simp only [CollatzResearch.WordTrace]
  refine ⟨296929909603232415151922321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197953273068821610101281547 296929909603232415151922321)
  ·
    refine ⟨222697432202424311363941741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296929909603232415151922321 222697432202424311363941741)
    ·
      refine ⟨83511537075909116761478153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222697432202424311363941741 83511537075909116761478153)
      ·
        refine ⟨62633652806931837571108615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83511537075909116761478153 62633652806931837571108615)
        ·
          refine ⟨93950479210397756356662923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62633652806931837571108615 93950479210397756356662923)
          ·
            refine ⟨140925718815596634534994385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93950479210397756356662923 140925718815596634534994385)
            ·
              refine ⟨105694289111697475901245789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140925718815596634534994385 105694289111697475901245789)
              ·
                refine ⟨39635358416886553462967171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105694289111697475901245789 39635358416886553462967171)
                ·
                  refine ⟨59453037625329830194450757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39635358416886553462967171 59453037625329830194450757)
                  ·
                    refine ⟨11147444554749343161459517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59453037625329830194450757 11147444554749343161459517)
                    ·
                      refine ⟨4180291708031003685547319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147444554749343161459517 4180291708031003685547319)
                      ·
                        rfl

theorem cell23_8141089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_8141089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141089 prefixEnd_8141089 := by exact prefixLift 8141089
  have htrace : WordTrace (prefixWord ++ tailWord_8141089) baseStart_8141089 baseEnd_8141089 := by
    simpa [prefixWord, tailWord_8141089, baseEnd_8141089] using wordTrace_append hprefix tailTrace_8141089
  have hstable : (prefixWord ++ tailWord_8141089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141089).length < 2 ^ (prefixWord ++ tailWord_8141089).sum := by decide
  have hdescent : baseEnd_8141089 < baseStart_8141089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141136 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 5, 1, 3]
def baseStart_8141136 : Nat := 118140960795 + 8141136 * 2 ^ 59
def prefixEnd_8141136 : Nat := 4983230072969 + 3 ^ 40 * 8141136 * 2
def baseEnd_8141136 : Nat := 4180315841621765001659603

theorem tailTrace_8141136 : CollatzResearch.WordTrace tailWord_8141136 prefixEnd_8141136 4180315841621765001659603 := by
  unfold tailWord_8141136
  simp only [CollatzResearch.WordTrace]
  refine ⟨148465811917031071089441631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197954415889374761452588841 148465811917031071089441631)
  ·
    refine ⟨222698717875546606634162447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148465811917031071089441631 222698717875546606634162447)
    ·
      refine ⟨334048076813319909951243671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222698717875546606634162447 334048076813319909951243671)
      ·
        refine ⟨501072115219979864926865507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334048076813319909951243671 501072115219979864926865507)
        ·
          refine ⟨751608172829969797390298261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501072115219979864926865507 751608172829969797390298261)
          ·
            refine ⟨35231633101404834252670231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 751608172829969797390298261 35231633101404834252670231)
            ·
              refine ⟨52847449652107251379005347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35231633101404834252670231 52847449652107251379005347)
              ·
                refine ⟨79271174478160877068508021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52847449652107251379005347 79271174478160877068508021)
                ·
                  refine ⟨7431672607327582225172627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79271174478160877068508021 7431672607327582225172627)
                  ·
                    refine ⟨11147508910991373337758941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431672607327582225172627 11147508910991373337758941)
                    ·
                      refine ⟨4180315841621765001659603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147508910991373337758941 4180315841621765001659603)
                      ·
                        rfl

theorem cell23_8141136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_8141136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141136 prefixEnd_8141136 := by exact prefixLift 8141136
  have htrace : WordTrace (prefixWord ++ tailWord_8141136) baseStart_8141136 baseEnd_8141136 := by
    simpa [prefixWord, tailWord_8141136, baseEnd_8141136] using wordTrace_append hprefix tailTrace_8141136
  have hstable : (prefixWord ++ tailWord_8141136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141136).length < 2 ^ (prefixWord ++ tailWord_8141136).sum := by decide
  have hdescent : baseEnd_8141136 < baseStart_8141136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141156 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_8141156 : Nat := 118140960795 + 8141156 * 2 ^ 59
def prefixEnd_8141156 : Nat := 4983230072969 + 3 ^ 40 * 8141156 * 2
def baseEnd_8141156 : Nat := 1393442037078284974469837

theorem tailTrace_8141156 : CollatzResearch.WordTrace tailWord_8141156 prefixEnd_8141156 1393442037078284974469837 := by
  unfold tailWord_8141156
  simp only [CollatzResearch.WordTrace]
  refine ⟨148466176646994842797305661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197954902195993123729740881 148466176646994842797305661)
  ·
    refine ⟨55674816242623066048989623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148466176646994842797305661 55674816242623066048989623)
    ·
      refine ⟨83512224363934599073484435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55674816242623066048989623 83512224363934599073484435)
      ·
        refine ⟨125268336545901898610226653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83512224363934599073484435 125268336545901898610226653)
        ·
          refine ⟨46975626204713211978834995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125268336545901898610226653 46975626204713211978834995)
          ·
            refine ⟨70463439307069817968252493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46975626204713211978834995 70463439307069817968252493)
            ·
              refine ⟨26423789740151181738094685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70463439307069817968252493 26423789740151181738094685)
              ·
                refine ⟨9908921152556693151785507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26423789740151181738094685 9908921152556693151785507)
                ·
                  refine ⟨14863381728835039727678261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908921152556693151785507 14863381728835039727678261)
                  ·
                    refine ⟨1393442037078284974469837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14863381728835039727678261 1393442037078284974469837)
                    ·
                      rfl

theorem cell23_8141156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_8141156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141156 prefixEnd_8141156 := by exact prefixLift 8141156
  have htrace : WordTrace (prefixWord ++ tailWord_8141156) baseStart_8141156 baseEnd_8141156 := by
    simpa [prefixWord, tailWord_8141156, baseEnd_8141156] using wordTrace_append hprefix tailTrace_8141156
  have hstable : (prefixWord ++ tailWord_8141156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141156).length < 2 ^ (prefixWord ++ tailWord_8141156).sum := by decide
  have hdescent : baseEnd_8141156 < baseStart_8141156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141170 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_8141170 : Nat := 118140960795 + 8141170 * 2 ^ 59
def prefixEnd_8141170 : Nat := 4983230072969 + 3 ^ 40 * 8141170 * 2
def baseEnd_8141170 : Nat := 4180333299964017868634447

theorem tailTrace_8141170 : CollatzResearch.WordTrace tailWord_8141170 prefixEnd_8141170 4180333299964017868634447 := by
  unfold tailWord_8141170
  simp only [CollatzResearch.WordTrace]
  refine ⟨74233215978984741496405241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197955242610625977323747309 74233215978984741496405241)
  ·
    refine ⟨55674911984238556122303931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74233215978984741496405241 55674911984238556122303931)
    ·
      refine ⟨83512367976357834183455897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55674911984238556122303931 83512367976357834183455897)
      ·
        refine ⟨62634275982268375637591923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83512367976357834183455897 62634275982268375637591923)
        ·
          refine ⟨93951413973402563456387885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62634275982268375637591923 93951413973402563456387885)
          ·
            refine ⟨35231780240025961296145457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93951413973402563456387885 35231780240025961296145457)
            ·
              refine ⟨26423835180019470972109093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35231780240025961296145457 26423835180019470972109093)
              ·
                refine ⟨4954469096253650807270455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26423835180019470972109093 4954469096253650807270455)
                ·
                  refine ⟨7431703644380476210905683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954469096253650807270455 7431703644380476210905683)
                  ·
                    refine ⟨11147555466570714316358525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431703644380476210905683 11147555466570714316358525)
                    ·
                      refine ⟨4180333299964017868634447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147555466570714316358525 4180333299964017868634447)
                      ·
                        rfl

theorem cell23_8141170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_8141170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141170 prefixEnd_8141170 := by exact prefixLift 8141170
  have htrace : WordTrace (prefixWord ++ tailWord_8141170) baseStart_8141170 baseEnd_8141170 := by
    simpa [prefixWord, tailWord_8141170, baseEnd_8141170] using wordTrace_append hprefix tailTrace_8141170
  have hstable : (prefixWord ++ tailWord_8141170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141170).length < 2 ^ (prefixWord ++ tailWord_8141170).sum := by decide
  have hdescent : baseEnd_8141170 < baseStart_8141170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141179 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5]
def baseStart_8141179 : Nat := 118140960795 + 8141179 * 2 ^ 59
def prefixEnd_8141179 : Nat := 4983230072969 + 3 ^ 40 * 8141179 * 2
def baseEnd_8141179 : Nat := 4180337921289908333421905

theorem tailTrace_8141179 : CollatzResearch.WordTrace tailWord_8141179 prefixEnd_8141179 4180337921289908333421905 := by
  unfold tailWord_8141179
  simp only [CollatzResearch.WordTrace]
  refine ⟨296933192172906360522698591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197955461448604240348465727 296933192172906360522698591)
  ·
    refine ⟨445399788259359540784047887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296933192172906360522698591 445399788259359540784047887)
    ·
      refine ⟨668099682389039311176071831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445399788259359540784047887 668099682389039311176071831)
      ·
        refine ⟨1002149523583558966764107747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668099682389039311176071831 1002149523583558966764107747)
        ·
          refine ⟨1503224285375338450146161621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002149523583558966764107747 1503224285375338450146161621)
          ·
            refine ⟨35231819188484494925300663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1503224285375338450146161621 35231819188484494925300663)
            ·
              refine ⟨52847728782726742387950995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35231819188484494925300663 52847728782726742387950995)
              ·
                refine ⟨79271593174090113581926493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52847728782726742387950995 79271593174090113581926493)
                ·
                  refine ⟨29726847440283792593222435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79271593174090113581926493 29726847440283792593222435)
                  ·
                    refine ⟨44590271160425688889833653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29726847440283792593222435 44590271160425688889833653)
                    ·
                      refine ⟨4180337921289908333421905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44590271160425688889833653 4180337921289908333421905)
                      ·
                        rfl

theorem cell23_8141179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_8141179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141179 prefixEnd_8141179 := by exact prefixLift 8141179
  have htrace : WordTrace (prefixWord ++ tailWord_8141179) baseStart_8141179 baseEnd_8141179 := by
    simpa [prefixWord, tailWord_8141179, baseEnd_8141179] using wordTrace_append hprefix tailTrace_8141179
  have hstable : (prefixWord ++ tailWord_8141179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141179).length < 2 ^ (prefixWord ++ tailWord_8141179).sum := by decide
  have hdescent : baseEnd_8141179 < baseStart_8141179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141193 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 4]
def baseStart_8141193 : Nat := 118140960795 + 8141193 * 2 ^ 59
def prefixEnd_8141193 : Nat := 4983230072969 + 3 ^ 40 * 8141193 * 2
def baseEnd_8141193 : Nat := 4180345110019071278646841

theorem tailTrace_8141193 : CollatzResearch.WordTrace tailWord_8141193 prefixEnd_8141193 4180345110019071278646841 := by
  unfold tailWord_8141193
  simp only [CollatzResearch.WordTrace]
  refine ⟨296933702794855640913708233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197955801863237093942472155 296933702794855640913708233)
  ·
    refine ⟨222700277096141730685281175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296933702794855640913708233 222700277096141730685281175)
    ·
      refine ⟨334050415644212596027921763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222700277096141730685281175 334050415644212596027921763)
      ·
        refine ⟨501075623466318894041882645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334050415644212596027921763 501075623466318894041882645)
        ·
          refine ⟨23487919849983698158213249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501075623466318894041882645 23487919849983698158213249)
          ·
            refine ⟨17615939887487773618659937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23487919849983698158213249 17615939887487773618659937)
            ·
              refine ⟨13211954915615830213994953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17615939887487773618659937 13211954915615830213994953)
              ·
                refine ⟨9908966186711872660496215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13211954915615830213994953 9908966186711872660496215)
                ·
                  refine ⟨14863449280067808990744323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908966186711872660496215 14863449280067808990744323)
                  ·
                    refine ⟨22295173920101713486116485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14863449280067808990744323 22295173920101713486116485)
                    ·
                      refine ⟨4180345110019071278646841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22295173920101713486116485 4180345110019071278646841)
                      ·
                        rfl

theorem cell23_8141193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_8141193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141193 prefixEnd_8141193 := by exact prefixLift 8141193
  have htrace : WordTrace (prefixWord ++ tailWord_8141193) baseStart_8141193 baseEnd_8141193 := by
    simpa [prefixWord, tailWord_8141193, baseEnd_8141193] using wordTrace_append hprefix tailTrace_8141193
  have hstable : (prefixWord ++ tailWord_8141193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141193).length < 2 ^ (prefixWord ++ tailWord_8141193).sum := by decide
  have hdescent : baseEnd_8141193 < baseStart_8141193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141204 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_8141204 : Nat := 118140960795 + 8141204 * 2 ^ 59
def prefixEnd_8141204 : Nat := 4983230072969 + 3 ^ 40 * 8141204 * 2
def baseEnd_8141204 : Nat := 4180350758306270735609291

theorem tailTrace_8141204 : CollatzResearch.WordTrace tailWord_8141204 prefixEnd_8141204 4180350758306270735609291 := by
  unfold tailWord_8141204
  simp only [CollatzResearch.WordTrace]
  refine ⟨148467051998907894896179333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197956069331877193194905777 148467051998907894896179333)
  ·
    refine ⟨27837572249795230293033625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148467051998907894896179333 27837572249795230293033625)
    ·
      refine ⟨20878179187346422719775219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27837572249795230293033625 20878179187346422719775219)
      ·
        refine ⟨31317268781019634079662829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20878179187346422719775219 31317268781019634079662829)
        ·
          refine ⟨11743975792882362779873561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31317268781019634079662829 11743975792882362779873561)
          ·
            refine ⟨8807981844661772084905171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11743975792882362779873561 8807981844661772084905171)
            ·
              refine ⟨13211972766992658127357757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807981844661772084905171 13211972766992658127357757)
              ·
                refine ⟨4954489787622246797759159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13211972766992658127357757 4954489787622246797759159)
                ·
                  refine ⟨7431734681433370196638739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954489787622246797759159 7431734681433370196638739)
                  ·
                    refine ⟨11147602022150055294958109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7431734681433370196638739 11147602022150055294958109)
                    ·
                      refine ⟨4180350758306270735609291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147602022150055294958109 4180350758306270735609291)
                      ·
                        rfl

theorem cell23_8141204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_8141204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141204 prefixEnd_8141204 := by exact prefixLift 8141204
  have htrace : WordTrace (prefixWord ++ tailWord_8141204) baseStart_8141204 baseEnd_8141204 := by
    simpa [prefixWord, tailWord_8141204, baseEnd_8141204] using wordTrace_append hprefix tailTrace_8141204
  have hstable : (prefixWord ++ tailWord_8141204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141204).length < 2 ^ (prefixWord ++ tailWord_8141204).sum := by decide
  have hdescent : baseEnd_8141204 < baseStart_8141204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141213 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_8141213 : Nat := 118140960795 + 8141213 * 2 ^ 59
def prefixEnd_8141213 : Nat := 4983230072969 + 3 ^ 40 * 8141213 * 2
def baseEnd_8141213 : Nat := 4180355379632161200396749

theorem tailTrace_8141213 : CollatzResearch.WordTrace tailWord_8141213 prefixEnd_8141213 4180355379632161200396749 := by
  unfold tailWord_8141213
  simp only [CollatzResearch.WordTrace]
  refine ⟨296934432254783184329436293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197956288169855456219624195 296934432254783184329436293)
  ·
    refine ⟨55675206047771847061769305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296934432254783184329436293 55675206047771847061769305)
    ·
      refine ⟨41756404535828885296326979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55675206047771847061769305 41756404535828885296326979)
      ·
        refine ⟨62634606803743327944490469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41756404535828885296326979 62634606803743327944490469)
        ·
          refine ⟨11743988775701873989591963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62634606803743327944490469 11743988775701873989591963)
          ·
            refine ⟨17615983163552810984387945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11743988775701873989591963 17615983163552810984387945)
            ·
              refine ⟨13211987372664608238290959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17615983163552810984387945 13211987372664608238290959)
              ·
                refine ⟨19817981058996912357436439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13211987372664608238290959 19817981058996912357436439)
                ·
                  refine ⟨29726971588495368536154659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19817981058996912357436439 29726971588495368536154659)
                  ·
                    refine ⟨44590457382743052804231989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29726971588495368536154659 44590457382743052804231989)
                    ·
                      refine ⟨4180355379632161200396749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44590457382743052804231989 4180355379632161200396749)
                      ·
                        rfl

theorem cell23_8141213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_8141213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141213 prefixEnd_8141213 := by exact prefixLift 8141213
  have htrace : WordTrace (prefixWord ++ tailWord_8141213) baseStart_8141213 baseEnd_8141213 := by
    simpa [prefixWord, tailWord_8141213, baseEnd_8141213] using wordTrace_append hprefix tailTrace_8141213
  have hstable : (prefixWord ++ tailWord_8141213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141213).length < 2 ^ (prefixWord ++ tailWord_8141213).sum := by decide
  have hdescent : baseEnd_8141213 < baseStart_8141213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141237 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_8141237 : Nat := 118140960795 + 8141237 * 2 ^ 59
def prefixEnd_8141237 : Nat := 4983230072969 + 3 ^ 40 * 8141237 * 2
def baseEnd_8141237 : Nat := 1393455901055956368832213

theorem tailTrace_8141237 : CollatzResearch.WordTrace tailWord_8141237 prefixEnd_8141237 1393455901055956368832213 := by
  unfold tailWord_8141237
  simp only [CollatzResearch.WordTrace]
  refine ⟨296935307606696236428309965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197956871737797490952206643 296935307606696236428309965)
  ·
    refine ⟨111350740352511088660616237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296935307606696236428309965 111350740352511088660616237)
    ·
      refine ⟨41756527632191658247731089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111350740352511088660616237 41756527632191658247731089)
      ·
        refine ⟨31317395724143743685798317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41756527632191658247731089 31317395724143743685798317)
        ·
          refine ⟨11744023396553903882174369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31317395724143743685798317 11744023396553903882174369)
          ·
            refine ⟨8808017547415427911630777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11744023396553903882174369 8808017547415427911630777)
            ·
              refine ⟨6606013160561570933723083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8808017547415427911630777 6606013160561570933723083)
              ·
                refine ⟨9909019740842356400584625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606013160561570933723083 9909019740842356400584625)
                ·
                  refine ⟨7431764805631767300438469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9909019740842356400584625 7431764805631767300438469)
                  ·
                    refine ⟨1393455901055956368832213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431764805631767300438469 1393455901055956368832213)
                    ·
                      rfl

theorem cell23_8141237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_8141237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141237 prefixEnd_8141237 := by exact prefixLift 8141237
  have htrace : WordTrace (prefixWord ++ tailWord_8141237) baseStart_8141237 baseEnd_8141237 := by
    simpa [prefixWord, tailWord_8141237, baseEnd_8141237] using wordTrace_append hprefix tailTrace_8141237
  have hstable : (prefixWord ++ tailWord_8141237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141237).length < 2 ^ (prefixWord ++ tailWord_8141237).sum := by decide
  have hdescent : baseEnd_8141237 < baseStart_8141237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141259 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 4, 6]
def baseStart_8141259 : Nat := 118140960795 + 8141259 * 2 ^ 59
def prefixEnd_8141259 : Nat := 4983230072969 + 3 ^ 40 * 8141259 * 2
def baseEnd_8141259 : Nat := 1393459666580756006807179

theorem tailTrace_8141259 : CollatzResearch.WordTrace tailWord_8141259 prefixEnd_8141259 1393459666580756006807179 := by
  unfold tailWord_8141259
  simp only [CollatzResearch.WordTrace]
  refine ⟨296936110012616534185610831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197957406675077689457073887 296936110012616534185610831)
  ·
    refine ⟨445404165018924801278416247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296936110012616534185610831 445404165018924801278416247)
    ·
      refine ⟨668106247528387201917624371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445404165018924801278416247 668106247528387201917624371)
      ·
        refine ⟨1002159371292580802876436557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668106247528387201917624371 1002159371292580802876436557)
        ·
          refine ⟨375809764234717801078663709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002159371292580802876436557 375809764234717801078663709)
          ·
            refine ⟨140928661588019175404498891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375809764234717801078663709 140928661588019175404498891)
            ·
              refine ⟨211392992382028763106748337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140928661588019175404498891 211392992382028763106748337)
              ·
                refine ⟨158544744286521572330061253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211392992382028763106748337 158544744286521572330061253)
                ·
                  refine ⟨29727139553722794811886485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158544744286521572330061253 29727139553722794811886485)
                  ·
                    refine ⟨1393459666580756006807179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29727139553722794811886485 1393459666580756006807179)
                    ·
                      rfl

theorem cell23_8141259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_8141259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141259 prefixEnd_8141259 := by exact prefixLift 8141259
  have htrace : WordTrace (prefixWord ++ tailWord_8141259) baseStart_8141259 baseEnd_8141259 := by
    simpa [prefixWord, tailWord_8141259, baseEnd_8141259] using wordTrace_append hprefix tailTrace_8141259
  have hstable : (prefixWord ++ tailWord_8141259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141259).length < 2 ^ (prefixWord ++ tailWord_8141259).sum := by decide
  have hdescent : baseEnd_8141259 < baseStart_8141259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141293 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_8141293 : Nat := 118140960795 + 8141293 * 2 ^ 59
def prefixEnd_8141293 : Nat := 4983230072969 + 3 ^ 40 * 8141293 * 2
def baseEnd_8141293 : Nat := 1393465486028173629132127

theorem tailTrace_8141293 : CollatzResearch.WordTrace tailWord_8141293 prefixEnd_8141293 1393465486028173629132127 := by
  unfold tailWord_8141293
  simp only [CollatzResearch.WordTrace]
  refine ⟨296937350094493357992348533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197958233396328905328232355 296937350094493357992348533)
  ·
    refine ⟨27837876571358752311782675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296937350094493357992348533 27837876571358752311782675)
    ·
      refine ⟨41756814857038128467674013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27837876571358752311782675 41756814857038128467674013)
      ·
        refine ⟨15658805571389298175377755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41756814857038128467674013 15658805571389298175377755)
        ·
          refine ⟨23488208357083947263066633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15658805571389298175377755 23488208357083947263066633)
          ·
            refine ⟨17616156267812960447299975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23488208357083947263066633 17616156267812960447299975)
            ·
              refine ⟨26424234401719440670949963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17616156267812960447299975 26424234401719440670949963)
              ·
                refine ⟨39636351602579161006424945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26424234401719440670949963 39636351602579161006424945)
                ·
                  refine ⟨29727263701934370754818709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39636351602579161006424945 29727263701934370754818709)
                  ·
                    refine ⟨1393465486028173629132127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29727263701934370754818709 1393465486028173629132127)
                    ·
                      rfl

theorem cell23_8141293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_8141293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141293 prefixEnd_8141293 := by exact prefixLift 8141293
  have htrace : WordTrace (prefixWord ++ tailWord_8141293) baseStart_8141293 baseEnd_8141293 := by
    simpa [prefixWord, tailWord_8141293, baseEnd_8141293] using wordTrace_append hprefix tailTrace_8141293
  have hstable : (prefixWord ++ tailWord_8141293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141293).length < 2 ^ (prefixWord ++ tailWord_8141293).sum := by decide
  have hdescent : baseEnd_8141293 < baseStart_8141293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141296 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_8141296 : Nat := 118140960795 + 8141296 * 2 ^ 59
def prefixEnd_8141296 : Nat := 4983230072969 + 3 ^ 40 * 8141296 * 2
def baseEnd_8141296 : Nat := 4180397998526484375658867

theorem tailTrace_8141296 : CollatzResearch.WordTrace tailWord_8141296 prefixEnd_8141296 4180397998526484375658867 := by
  unfold tailWord_8141296
  simp only [CollatzResearch.WordTrace]
  refine ⟨148468729756741244752353871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197958306342321659669805161 148468729756741244752353871)
  ·
    refine ⟨222703094635111867128530807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148468729756741244752353871 222703094635111867128530807)
    ·
      refine ⟨334054641952667800692796211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222703094635111867128530807 334054641952667800692796211)
      ·
        refine ⟨501081962929001701039194317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334054641952667800692796211 501081962929001701039194317)
        ·
          refine ⟨187905736098375637889697869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501081962929001701039194317 187905736098375637889697869)
          ·
            refine ⟨70464651036890864208636701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187905736098375637889697869 70464651036890864208636701)
            ·
              refine ⟨26424244138834074078238763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70464651036890864208636701 26424244138834074078238763)
              ·
                refine ⟨39636366208251111117358145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26424244138834074078238763 39636366208251111117358145)
                ·
                  refine ⟨29727274656188333338018609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39636366208251111117358145 29727274656188333338018609)
                  ·
                    refine ⟨22295455992141250003513957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29727274656188333338018609 22295455992141250003513957)
                    ·
                      refine ⟨4180397998526484375658867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22295455992141250003513957 4180397998526484375658867)
                      ·
                        rfl

theorem cell23_8141296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_8141296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141296 prefixEnd_8141296 := by exact prefixLift 8141296
  have htrace : WordTrace (prefixWord ++ tailWord_8141296) baseStart_8141296 baseEnd_8141296 := by
    simpa [prefixWord, tailWord_8141296, baseEnd_8141296] using wordTrace_append hprefix tailTrace_8141296
  have hstable : (prefixWord ++ tailWord_8141296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141296).length < 2 ^ (prefixWord ++ tailWord_8141296).sum := by decide
  have hdescent : baseEnd_8141296 < baseStart_8141296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141323 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 5]
def baseStart_8141323 : Nat := 118140960795 + 8141323 * 2 ^ 59
def prefixEnd_8141323 : Nat := 4983230072969 + 3 ^ 40 * 8141323 * 2
def baseEnd_8141323 : Nat := 464490206944906196669027

theorem tailTrace_8141323 : CollatzResearch.WordTrace tailWord_8141323 prefixEnd_8141323 464490206944906196669027 := by
  unfold tailWord_8141323
  simp only [CollatzResearch.WordTrace]
  refine ⟨296938444284384673115940623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197958962856256448743960415 296938444284384673115940623)
  ·
    refine ⟨445407666426577009673910935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296938444284384673115940623 445407666426577009673910935)
    ·
      refine ⟨668111499639865514510866403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445407666426577009673910935 668111499639865514510866403)
      ·
        refine ⟨1002167249459798271766299605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668111499639865514510866403 1002167249459798271766299605)
        ·
          refine ⟨23488294909214021994522647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1002167249459798271766299605 23488294909214021994522647)
          ·
            refine ⟨35232442363821032991783971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23488294909214021994522647 35232442363821032991783971)
            ·
              refine ⟨52848663545731549487675957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35232442363821032991783971 52848663545731549487675957)
              ·
                refine ⟨4954562207412332764469621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52848663545731549487675957 4954562207412332764469621)
                ·
                  refine ⟨464490206944906196669027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954562207412332764469621 464490206944906196669027)
                  ·
                    rfl

theorem cell23_8141323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 5].length) (baseStart_8141323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141323 prefixEnd_8141323 := by exact prefixLift 8141323
  have htrace : WordTrace (prefixWord ++ tailWord_8141323) baseStart_8141323 baseEnd_8141323 := by
    simpa [prefixWord, tailWord_8141323, baseEnd_8141323] using wordTrace_append hprefix tailTrace_8141323
  have hstable : (prefixWord ++ tailWord_8141323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141323).length < 2 ^ (prefixWord ++ tailWord_8141323).sum := by decide
  have hdescent : baseEnd_8141323 < baseStart_8141323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141346 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_8141346 : Nat := 118140960795 + 8141346 * 2 ^ 59
def prefixEnd_8141346 : Nat := 4983230072969 + 3 ^ 40 * 8141346 * 2
def baseEnd_8141346 : Nat := 4180423672559209180033637

theorem tailTrace_8141346 : CollatzResearch.WordTrace tailWord_8141346 prefixEnd_8141346 4180423672559209180033637 := by
  unfold tailWord_8141346
  simp only [CollatzResearch.WordTrace]
  refine ⟨74234820790825337011006973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197959522108867565362685261 74234820790825337011006973)
  ·
    refine ⟨27838057796559501379127615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74234820790825337011006973 27838057796559501379127615)
    ·
      refine ⟨41757086694839252068691423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27838057796559501379127615 41757086694839252068691423)
      ·
        refine ⟨62635630042258878103037135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41757086694839252068691423 62635630042258878103037135)
        ·
          refine ⟨93953445063388317154555703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62635630042258878103037135 93953445063388317154555703)
          ·
            refine ⟨140930167595082475731833555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93953445063388317154555703 140930167595082475731833555)
            ·
              refine ⟨211395251392623713597750333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140930167595082475731833555 211395251392623713597750333)
              ·
                refine ⟨79273219272233892599156375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211395251392623713597750333 79273219272233892599156375)
                ·
                  refine ⟨118909828908350838898734563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79273219272233892599156375 118909828908350838898734563)
                  ·
                    refine ⟨178364743362526258348101845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118909828908350838898734563 178364743362526258348101845)
                    ·
                      refine ⟨4180423672559209180033637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178364743362526258348101845 4180423672559209180033637)
                      ·
                        rfl

theorem cell23_8141346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_8141346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141346 prefixEnd_8141346 := by exact prefixLift 8141346
  have htrace : WordTrace (prefixWord ++ tailWord_8141346) baseStart_8141346 baseEnd_8141346 := by
    simpa [prefixWord, tailWord_8141346, baseEnd_8141346] using wordTrace_append hprefix tailTrace_8141346
  have hstable : (prefixWord ++ tailWord_8141346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141346).length < 2 ^ (prefixWord ++ tailWord_8141346).sum := by decide
  have hdescent : baseEnd_8141346 < baseStart_8141346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141351 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_8141351 : Nat := 118140960795 + 8141351 * 2 ^ 59
def prefixEnd_8141351 : Nat := 4983230072969 + 3 ^ 40 * 8141351 * 2
def baseEnd_8141351 : Nat := 4180426239962481660471115

theorem tailTrace_8141351 : CollatzResearch.WordTrace tailWord_8141351 prefixEnd_8141351 4180426239962481660471115 := by
  unfold tailWord_8141351
  simp only [CollatzResearch.WordTrace]
  refine ⟨296939465528283233897959907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197959643685522155931973271 296939465528283233897959907)
  ·
    refine ⟨445409198292424850846939861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296939465528283233897959907 445409198292424850846939861)
    ·
      refine ⟨10439278084978707441725153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 445409198292424850846939861 10439278084978707441725153)
      ·
        refine ⟨7829458563734030581293865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10439278084978707441725153 7829458563734030581293865)
        ·
          refine ⟨5872093922800522935970399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7829458563734030581293865 5872093922800522935970399)
          ·
            refine ⟨8808140884200784403955599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872093922800522935970399 8808140884200784403955599)
            ·
              refine ⟨13212211326301176605933399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808140884200784403955599 13212211326301176605933399)
              ·
                refine ⟨19818316989451764908900099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212211326301176605933399 19818316989451764908900099)
                ·
                  refine ⟨29727475484177647363350149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19818316989451764908900099 29727475484177647363350149)
                  ·
                    refine ⟨5573901653283308880628153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29727475484177647363350149 5573901653283308880628153)
                    ·
                      refine ⟨4180426239962481660471115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5573901653283308880628153 4180426239962481660471115)
                      ·
                        rfl

theorem cell23_8141351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_8141351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141351 prefixEnd_8141351 := by exact prefixLift 8141351
  have htrace : WordTrace (prefixWord ++ tailWord_8141351) baseStart_8141351 baseEnd_8141351 := by
    simpa [prefixWord, tailWord_8141351, baseEnd_8141351] using wordTrace_append hprefix tailTrace_8141351
  have hstable : (prefixWord ++ tailWord_8141351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141351).length < 2 ^ (prefixWord ++ tailWord_8141351).sum := by decide
  have hdescent : baseEnd_8141351 < baseStart_8141351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141373 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_8141373 : Nat := 118140960795 + 8141373 * 2 ^ 59
def prefixEnd_8141373 : Nat := 4983230072969 + 3 ^ 40 * 8141373 * 2
def baseEnd_8141373 : Nat := 4180437536536880574396013

theorem tailTrace_8141373 : CollatzResearch.WordTrace tailWord_8141373 prefixEnd_8141373 4180437536536880574396013 := by
  unfold tailWord_8141373
  simp only [CollatzResearch.WordTrace]
  refine ⟨296940267934203531655260773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197960178622802354436840515 296940267934203531655260773)
  ·
    refine ⟨55676300237663162185361395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296940267934203531655260773 55676300237663162185361395)
    ·
      refine ⟨83514450356494743278042093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55676300237663162185361395 83514450356494743278042093)
      ·
        refine ⟨31317918883685528729265785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83514450356494743278042093 31317918883685528729265785)
        ·
          refine ⟨23488439162764146546949339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31317918883685528729265785 23488439162764146546949339)
          ·
            refine ⟨35232658744146219820424009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23488439162764146546949339 35232658744146219820424009)
            ·
              refine ⟨26424494058109664865318007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35232658744146219820424009 26424494058109664865318007)
              ·
                refine ⟨39636741087164497297977011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26424494058109664865318007 39636741087164497297977011)
                ·
                  refine ⟨59455111630746745946965517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39636741087164497297977011 59455111630746745946965517)
                  ·
                    refine ⟨22295666861530029730112069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59455111630746745946965517 22295666861530029730112069)
                    ·
                      refine ⟨4180437536536880574396013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22295666861530029730112069 4180437536536880574396013)
                      ·
                        rfl

theorem cell23_8141373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_8141373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141373 prefixEnd_8141373 := by exact prefixLift 8141373
  have htrace : WordTrace (prefixWord ++ tailWord_8141373) baseStart_8141373 baseEnd_8141373 := by
    simpa [prefixWord, tailWord_8141373, baseEnd_8141373] using wordTrace_append hprefix tailTrace_8141373
  have hstable : (prefixWord ++ tailWord_8141373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141373).length < 2 ^ (prefixWord ++ tailWord_8141373).sum := by decide
  have hdescent : baseEnd_8141373 < baseStart_8141373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141374 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_8141374 : Nat := 118140960795 + 8141374 * 2 ^ 59
def prefixEnd_8141374 : Nat := 4983230072969 + 3 ^ 40 * 8141374 * 2
def baseEnd_8141374 : Nat := 464493116668615007831501

theorem tailTrace_8141374 : CollatzResearch.WordTrace tailWord_8141374 prefixEnd_8141374 464493116668615007831501 := by
  unfold tailWord_8141374
  simp only [CollatzResearch.WordTrace]
  refine ⟨37117538050899988603255897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197960202938133272550698117 37117538050899988603255897)
  ·
    refine ⟨27838153538174991452441923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37117538050899988603255897 27838153538174991452441923)
    ·
      refine ⟨41757230307262487178662885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27838153538174991452441923 41757230307262487178662885)
      ·
        refine ⟨7829480682611716345999291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41757230307262487178662885 7829480682611716345999291)
        ·
          refine ⟨11744221023917574518998937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829480682611716345999291 11744221023917574518998937)
          ·
            refine ⟨8808165767938180889249203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11744221023917574518998937 8808165767938180889249203)
            ·
              refine ⟨13212248651907271333873805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808165767938180889249203 13212248651907271333873805)
              ·
                refine ⟨4954593244465226750202677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13212248651907271333873805 4954593244465226750202677)
                ·
                  refine ⟨464493116668615007831501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954593244465226750202677 464493116668615007831501)
                  ·
                    rfl

theorem cell23_8141374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_8141374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141374 prefixEnd_8141374 := by exact prefixLift 8141374
  have htrace : WordTrace (prefixWord ++ tailWord_8141374) baseStart_8141374 baseEnd_8141374 := by
    simpa [prefixWord, tailWord_8141374, baseEnd_8141374] using wordTrace_append hprefix tailTrace_8141374
  have hstable : (prefixWord ++ tailWord_8141374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141374).length < 2 ^ (prefixWord ++ tailWord_8141374).sum := by decide
  have hdescent : baseEnd_8141374 < baseStart_8141374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141393 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_8141393 : Nat := 118140960795 + 8141393 * 2 ^ 59
def prefixEnd_8141393 : Nat := 4983230072969 + 3 ^ 40 * 8141393 * 2
def baseEnd_8141393 : Nat := 4180447806149970496145921

theorem tailTrace_8141393 : CollatzResearch.WordTrace tailWord_8141393 prefixEnd_8141393 4180447806149970496145921 := by
  unfold tailWord_8141393
  simp only [CollatzResearch.WordTrace]
  refine ⟨296940997394131075070988833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197960664929420716713992555 296940997394131075070988833)
  ·
    refine ⟨222705748045598306303241625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296940997394131075070988833 222705748045598306303241625)
    ·
      refine ⟨167029311034198729727431219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222705748045598306303241625 167029311034198729727431219)
      ·
        refine ⟨250543966551298094591146829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167029311034198729727431219 250543966551298094591146829)
        ·
          refine ⟨93953987456736785471680061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250543966551298094591146829 93953987456736785471680061)
          ·
            refine ⟨35232745296276294551880023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93953987456736785471680061 35232745296276294551880023)
            ·
              refine ⟨52849117944414441827820035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35232745296276294551880023 52849117944414441827820035)
              ·
                refine ⟨79273676916621662741730053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52849117944414441827820035 79273676916621662741730053)
                ·
                  refine ⟨14863814421866561764074385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79273676916621662741730053 14863814421866561764074385)
                  ·
                    refine ⟨11147860816399921323055789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14863814421866561764074385 11147860816399921323055789)
                    ·
                      refine ⟨4180447806149970496145921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11147860816399921323055789 4180447806149970496145921)
                      ·
                        rfl

theorem cell23_8141393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_8141393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141393 prefixEnd_8141393 := by exact prefixLift 8141393
  have htrace : WordTrace (prefixWord ++ tailWord_8141393) baseStart_8141393 baseEnd_8141393 := by
    simpa [prefixWord, tailWord_8141393, baseEnd_8141393] using wordTrace_append hprefix tailTrace_8141393
  have hstable : (prefixWord ++ tailWord_8141393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141393).length < 2 ^ (prefixWord ++ tailWord_8141393).sum := by decide
  have hdescent : baseEnd_8141393 < baseStart_8141393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141400 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 1, 4]
def baseStart_8141400 : Nat := 118140960795 + 8141400 * 2 ^ 59
def prefixEnd_8141400 : Nat := 4983230072969 + 3 ^ 40 * 8141400 * 2
def baseEnd_8141400 : Nat := 1393483800171517322919463

theorem tailTrace_8141400 : CollatzResearch.WordTrace tailWord_8141400 prefixEnd_8141400 1393483800171517322919463 := by
  unfold tailWord_8141400
  simp only [CollatzResearch.WordTrace]
  refine ⟨148470626352552857633246827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197960835136737143510995769 148470626352552857633246827)
  ·
    refine ⟨222705939528829286449870241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148470626352552857633246827 222705939528829286449870241)
    ·
      refine ⟨167029454646621964837402681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222705939528829286449870241 167029454646621964837402681)
      ·
        refine ⟨125272090984966473628052011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167029454646621964837402681 125272090984966473628052011)
        ·
          refine ⟨187908136477449710442078017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125272090984966473628052011 187908136477449710442078017)
          ·
            refine ⟨140931102358087282831558513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187908136477449710442078017 140931102358087282831558513)
            ·
              refine ⟨105698326768565462123668885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140931102358087282831558513 105698326768565462123668885)
              ·
                refine ⟨4954609067276506037046979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105698326768565462123668885 4954609067276506037046979)
                ·
                  refine ⟨7431913600914759055570469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954609067276506037046979 7431913600914759055570469)
                  ·
                    refine ⟨1393483800171517322919463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431913600914759055570469 1393483800171517322919463)
                    ·
                      rfl

theorem cell23_8141400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_8141400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141400 prefixEnd_8141400 := by exact prefixLift 8141400
  have htrace : WordTrace (prefixWord ++ tailWord_8141400) baseStart_8141400 baseEnd_8141400 := by
    simpa [prefixWord, tailWord_8141400, baseEnd_8141400] using wordTrace_append hprefix tailTrace_8141400
  have hstable : (prefixWord ++ tailWord_8141400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141400).length < 2 ^ (prefixWord ++ tailWord_8141400).sum := by decide
  have hdescent : baseEnd_8141400 < baseStart_8141400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141443 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 1, 5]
def baseStart_8141443 : Nat := 118140960795 + 8141443 * 2 ^ 59
def prefixEnd_8141443 : Nat := 4983230072969 + 3 ^ 40 * 8141443 * 2
def baseEnd_8141443 : Nat := 1393491160060898433506897

theorem tailTrace_8141443 : CollatzResearch.WordTrace tailWord_8141443 prefixEnd_8141443 1393491160060898433506897 := by
  unfold tailWord_8141443
  simp only [CollatzResearch.WordTrace]
  refine ⟨296942821043949933610308983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197961880695966622406872655 296942821043949933610308983)
  ·
    refine ⟨445414231565924900415463475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296942821043949933610308983 445414231565924900415463475)
    ·
      refine ⟨668121347348887350623195213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445414231565924900415463475 668121347348887350623195213)
      ·
        refine ⟨250545505255832756483698205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668121347348887350623195213 250545505255832756483698205)
        ·
          refine ⟨93954564470937283681386827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250545505255832756483698205 93954564470937283681386827)
          ·
            refine ⟨140931846706405925522080241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93954564470937283681386827 140931846706405925522080241)
            ·
              refine ⟨105698885029804444141560181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140931846706405925522080241 105698885029804444141560181)
              ·
                refine ⟨9909270471544166638271267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105698885029804444141560181 9909270471544166638271267)
                ·
                  refine ⟨14863905707316249957406901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909270471544166638271267 14863905707316249957406901)
                  ·
                    refine ⟨1393491160060898433506897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14863905707316249957406901 1393491160060898433506897)
                    ·
                      rfl

theorem cell23_8141443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 5].length) (baseStart_8141443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141443 prefixEnd_8141443 := by exact prefixLift 8141443
  have htrace : WordTrace (prefixWord ++ tailWord_8141443) baseStart_8141443 baseEnd_8141443 := by
    simpa [prefixWord, tailWord_8141443, baseEnd_8141443] using wordTrace_append hprefix tailTrace_8141443
  have hstable : (prefixWord ++ tailWord_8141443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141443).length < 2 ^ (prefixWord ++ tailWord_8141443).sum := by decide
  have hdescent : baseEnd_8141443 < baseStart_8141443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141460 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_8141460 : Nat := 118140960795 + 8141460 * 2 ^ 59
def prefixEnd_8141460 : Nat := 4983230072969 + 3 ^ 40 * 8141460 * 2
def baseEnd_8141460 : Nat := 1393494069784607244669371

theorem tailTrace_8141460 : CollatzResearch.WordTrace tailWord_8141460 prefixEnd_8141460 1393494069784607244669371 := by
  unfold tailWord_8141460
  simp only [CollatzResearch.WordTrace]
  refine ⟨148471720542444172756838917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197962294056592230342451889 148471720542444172756838917)
  ·
    refine ⟨27838447601708282391907297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148471720542444172756838917 27838447601708282391907297)
    ·
      refine ⟨20878835701281211793930473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27838447601708282391907297 20878835701281211793930473)
      ·
        refine ⟨15659126775960908845447855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20878835701281211793930473 15659126775960908845447855)
        ·
          refine ⟨23488690163941363268171783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15659126775960908845447855 23488690163941363268171783)
          ·
            refine ⟨35233035245912044902257675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23488690163941363268171783 35233035245912044902257675)
            ·
              refine ⟨52849552868868067353386513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35233035245912044902257675 52849552868868067353386513)
              ·
                refine ⟨39637164651651050515039885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52849552868868067353386513 39637164651651050515039885)
                ·
                  refine ⟨14863936744369143943139957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39637164651651050515039885 14863936744369143943139957)
                  ·
                    refine ⟨1393494069784607244669371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14863936744369143943139957 1393494069784607244669371)
                    ·
                      rfl

theorem cell23_8141460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_8141460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141460 prefixEnd_8141460 := by exact prefixLift 8141460
  have htrace : WordTrace (prefixWord ++ tailWord_8141460) baseStart_8141460 baseEnd_8141460 := by
    simpa [prefixWord, tailWord_8141460, baseEnd_8141460] using wordTrace_append hprefix tailTrace_8141460
  have hstable : (prefixWord ++ tailWord_8141460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141460).length < 2 ^ (prefixWord ++ tailWord_8141460).sum := by decide
  have hdescent : baseEnd_8141460 < baseStart_8141460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141463 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_8141463 : Nat := 118140960795 + 8141463 * 2 ^ 59
def prefixEnd_8141463 : Nat := 4983230072969 + 3 ^ 40 * 8141463 * 2
def baseEnd_8141463 : Nat := 4180483749795785222270599

theorem tailTrace_8141463 : CollatzResearch.WordTrace tailWord_8141463 prefixEnd_8141463 4180483749795785222270599 := by
  unfold tailWord_8141463
  simp only [CollatzResearch.WordTrace]
  refine ⟨296943550503877477026037043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197962367002584984684024695 296943550503877477026037043)
  ·
    refine ⟨445415325755816215539055565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296943550503877477026037043 445415325755816215539055565)
    ·
      refine ⟨167030747158431080827145837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445415325755816215539055565 167030747158431080827145837)
      ·
        refine ⟨62636530184411655310179689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167030747158431080827145837 62636530184411655310179689)
        ·
          refine ⟨46977397638308741482634767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62636530184411655310179689 46977397638308741482634767)
          ·
            refine ⟨70466096457463112223952151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46977397638308741482634767 70466096457463112223952151)
            ·
              refine ⟨105699144686194668335928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70466096457463112223952151 105699144686194668335928227)
              ·
                refine ⟨158548717029292002503892341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105699144686194668335928227 158548717029292002503892341)
                ·
                  refine ⟨14863942221496125234739907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158548717029292002503892341 14863942221496125234739907)
                  ·
                    refine ⟨22295913332244187852109861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14863942221496125234739907 22295913332244187852109861)
                    ·
                      refine ⟨4180483749795785222270599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22295913332244187852109861 4180483749795785222270599)
                      ·
                        rfl

theorem cell23_8141463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_8141463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141463 prefixEnd_8141463 := by exact prefixLift 8141463
  have htrace : WordTrace (prefixWord ++ tailWord_8141463) baseStart_8141463 baseEnd_8141463 := by
    simpa [prefixWord, tailWord_8141463, baseEnd_8141463] using wordTrace_append hprefix tailTrace_8141463
  have hstable : (prefixWord ++ tailWord_8141463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141463).length < 2 ^ (prefixWord ++ tailWord_8141463).sum := by decide
  have hdescent : baseEnd_8141463 < baseStart_8141463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141494 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_8141494 : Nat := 118140960795 + 8141494 * 2 ^ 59
def prefixEnd_8141494 : Nat := 4983230072969 + 3 ^ 40 * 8141494 * 2
def baseEnd_8141494 : Nat := 1393499889232024866994319

theorem tailTrace_8141494 : CollatzResearch.WordTrace tailWord_8141494 prefixEnd_8141494 1393499889232024866994319 := by
  unfold tailWord_8141494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559042572922823082525971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197963120777843446213610357 18559042572922823082525971)
  ·
    refine ⟨27838563859384234623788957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18559042572922823082525971 27838563859384234623788957)
    ·
      refine ⟨10439461447269087983920859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27838563859384234623788957 10439461447269087983920859)
      ·
        refine ⟨15659192170903631975881289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10439461447269087983920859 15659192170903631975881289)
        ·
          refine ⟨11744394128177723981910967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15659192170903631975881289 11744394128177723981910967)
          ·
            refine ⟨17616591192266585972866451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744394128177723981910967 17616591192266585972866451)
            ·
              refine ⟨26424886788399878959299677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17616591192266585972866451 26424886788399878959299677)
              ·
                refine ⟨9909332545649954609737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26424886788399878959299677 9909332545649954609737379)
                ·
                  refine ⟨14863998818474931914606069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909332545649954609737379 14863998818474931914606069)
                  ·
                    refine ⟨1393499889232024866994319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14863998818474931914606069 1393499889232024866994319)
                    ·
                      rfl

theorem cell23_8141494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_8141494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141494 prefixEnd_8141494 := by exact prefixLift 8141494
  have htrace : WordTrace (prefixWord ++ tailWord_8141494) baseStart_8141494 baseEnd_8141494 := by
    simpa [prefixWord, tailWord_8141494, baseEnd_8141494] using wordTrace_append hprefix tailTrace_8141494
  have hstable : (prefixWord ++ tailWord_8141494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141494).length < 2 ^ (prefixWord ++ tailWord_8141494).sum := by decide
  have hdescent : baseEnd_8141494 < baseStart_8141494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141514 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_8141514 : Nat := 118140960795 + 8141514 * 2 ^ 59
def prefixEnd_8141514 : Nat := 4983230072969 + 3 ^ 40 * 8141514 * 2
def baseEnd_8141514 : Nat := 4180509937309164522732865

theorem tailTrace_8141514 : CollatzResearch.WordTrace tailWord_8141514 prefixEnd_8141514 4180509937309164522732865 := by
  unfold tailWord_8141514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74236352656673178184035899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197963607084461808490762397 74236352656673178184035899)
  ·
    refine ⟨111354528985009767276053849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74236352656673178184035899 111354528985009767276053849)
    ·
      refine ⟨83515896738757325457040387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111354528985009767276053849 83515896738757325457040387)
      ·
        refine ⟨125273845108135988185560581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83515896738757325457040387 125273845108135988185560581)
        ·
          refine ⟨23488845957775497784792609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125273845108135988185560581 23488845957775497784792609)
          ·
            refine ⟨17616634468331623338594457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23488845957775497784792609 17616634468331623338594457)
            ·
              refine ⟨13212475851248717503945843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17616634468331623338594457 13212475851248717503945843)
              ·
                refine ⟨19818713776873076255918765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212475851248717503945843 19818713776873076255918765)
                ·
                  refine ⟨7432017666327403595969537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19818713776873076255918765 7432017666327403595969537)
                  ·
                    refine ⟨5574013249745552696977153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7432017666327403595969537 5574013249745552696977153)
                    ·
                      refine ⟨4180509937309164522732865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574013249745552696977153 4180509937309164522732865)
                      ·
                        rfl

theorem cell23_8141514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_8141514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141514 prefixEnd_8141514 := by exact prefixLift 8141514
  have htrace : WordTrace (prefixWord ++ tailWord_8141514) baseStart_8141514 baseEnd_8141514 := by
    simpa [prefixWord, tailWord_8141514, baseEnd_8141514] using wordTrace_append hprefix tailTrace_8141514
  have hstable : (prefixWord ++ tailWord_8141514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141514).length < 2 ^ (prefixWord ++ tailWord_8141514).sum := by decide
  have hdescent : baseEnd_8141514 < baseStart_8141514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141524 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_8141524 : Nat := 118140960795 + 8141524 * 2 ^ 59
def prefixEnd_8141524 : Nat := 4983230072969 + 3 ^ 40 * 8141524 * 2
def baseEnd_8141524 : Nat := 1393505024038569827869273

theorem tailTrace_8141524 : CollatzResearch.WordTrace tailWord_8141524 prefixEnd_8141524 1393505024038569827869273 := by
  unfold tailWord_8141524
  simp only [CollatzResearch.WordTrace]
  refine ⟨148472887678328242222003813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197963850237770989629338417 148472887678328242222003813)
  ·
    refine ⟨27838666439686545416625715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148472887678328242222003813 27838666439686545416625715)
    ·
      refine ⟨41757999659529818124938573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27838666439686545416625715 41757999659529818124938573)
      ·
        refine ⟨15659249872323681796851965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41757999659529818124938573 15659249872323681796851965)
        ·
          refine ⟨5872218702121380673819487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15659249872323681796851965 5872218702121380673819487)
          ·
            refine ⟨8808328053182071010729231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872218702121380673819487 8808328053182071010729231)
            ·
              refine ⟨13212492079773106516093847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808328053182071010729231 13212492079773106516093847)
              ·
                refine ⟨19818738119659659774140771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212492079773106516093847 19818738119659659774140771)
                ·
                  refine ⟨29728107179489489661211157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19818738119659659774140771 29728107179489489661211157)
                  ·
                    refine ⟨1393505024038569827869273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29728107179489489661211157 1393505024038569827869273)
                    ·
                      rfl

theorem cell23_8141524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_8141524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141524 prefixEnd_8141524 := by exact prefixLift 8141524
  have htrace : WordTrace (prefixWord ++ tailWord_8141524) baseStart_8141524 baseEnd_8141524 := by
    simpa [prefixWord, tailWord_8141524, baseEnd_8141524] using wordTrace_append hprefix tailTrace_8141524
  have hstable : (prefixWord ++ tailWord_8141524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141524).length < 2 ^ (prefixWord ++ tailWord_8141524).sum := by decide
  have hdescent : baseEnd_8141524 < baseStart_8141524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141583 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_8141583 : Nat := 118140960795 + 8141583 * 2 ^ 59
def prefixEnd_8141583 : Nat := 4983230072969 + 3 ^ 40 * 8141583 * 2
def baseEnd_8141583 : Nat := 4180545367474324752770047

theorem tailTrace_8141583 : CollatzResearch.WordTrace tailWord_8141583 prefixEnd_8141583 4180545367474324752770047 := by
  unfold tailWord_8141583
  simp only [CollatzResearch.WordTrace]
  refine ⟨296947927263442737520405403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197965284842295158346936935 296947927263442737520405403)
  ·
    refine ⟨445421890895164106280608105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296947927263442737520405403 445421890895164106280608105)
    ·
      refine ⟨334066418171373079710456079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445421890895164106280608105 334066418171373079710456079)
      ·
        refine ⟨501099627257059619565684119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334066418171373079710456079 501099627257059619565684119)
        ·
          refine ⟨751649440885589429348526179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501099627257059619565684119 751649440885589429348526179)
          ·
            refine ⟨1127474161328384144022789269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751649440885589429348526179 1127474161328384144022789269)
            ·
              refine ⟨52850351312268006751068247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1127474161328384144022789269 52850351312268006751068247)
              ·
                refine ⟨79275526968402010126602371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52850351312268006751068247 79275526968402010126602371)
                ·
                  refine ⟨118913290452603015189903557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79275526968402010126602371 118913290452603015189903557)
                  ·
                    refine ⟨22296241959863065348106917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118913290452603015189903557 22296241959863065348106917)
                    ·
                      refine ⟨4180545367474324752770047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22296241959863065348106917 4180545367474324752770047)
                      ·
                        rfl

theorem cell23_8141583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_8141583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141583 prefixEnd_8141583 := by exact prefixLift 8141583
  have htrace : WordTrace (prefixWord ++ tailWord_8141583) baseStart_8141583 baseEnd_8141583 := by
    simpa [prefixWord, tailWord_8141583, baseEnd_8141583] using wordTrace_append hprefix tailTrace_8141583
  have hstable : (prefixWord ++ tailWord_8141583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141583).length < 2 ^ (prefixWord ++ tailWord_8141583).sum := by decide
  have hdescent : baseEnd_8141583 < baseStart_8141583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141591 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 1, 3, 2]
def baseStart_8141591 : Nat := 118140960795 + 8141591 * 2 ^ 59
def prefixEnd_8141591 : Nat := 4983230072969 + 3 ^ 40 * 8141591 * 2
def baseEnd_8141591 : Nat := 4180549475319560721470011

theorem tailTrace_8141591 : CollatzResearch.WordTrace tailWord_8141591 prefixEnd_8141591 4180549475319560721470011 := by
  unfold tailWord_8141591
  simp only [CollatzResearch.WordTrace]
  refine ⟨296948219047413754886696627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197965479364942503257797751 296948219047413754886696627)
  ·
    refine ⟨445422328571120632330044941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296948219047413754886696627 445422328571120632330044941)
    ·
      refine ⟨167033373214170237123766853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445422328571120632330044941 167033373214170237123766853)
      ·
        refine ⟨31318757477656919460706285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167033373214170237123766853 31318757477656919460706285)
        ·
          refine ⟨11744534054121344797764857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31318757477656919460706285 11744534054121344797764857)
          ·
            refine ⟨8808400540591008598323643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11744534054121344797764857 8808400540591008598323643)
            ·
              refine ⟨13212600810886512897485465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808400540591008598323643 13212600810886512897485465)
              ·
                refine ⟨9909450608164884673114099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13212600810886512897485465 9909450608164884673114099)
                ·
                  refine ⟨14864175912247327009671149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909450608164884673114099 14864175912247327009671149)
                  ·
                    refine ⟨5574065967092747628626681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14864175912247327009671149 5574065967092747628626681)
                    ·
                      refine ⟨4180549475319560721470011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574065967092747628626681 4180549475319560721470011)
                      ·
                        rfl

theorem cell23_8141591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_8141591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141591 prefixEnd_8141591 := by exact prefixLift 8141591
  have htrace : WordTrace (prefixWord ++ tailWord_8141591) baseStart_8141591 baseEnd_8141591 := by
    simpa [prefixWord, tailWord_8141591, baseEnd_8141591] using wordTrace_append hprefix tailTrace_8141591
  have hstable : (prefixWord ++ tailWord_8141591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141591).length < 2 ^ (prefixWord ++ tailWord_8141591).sum := by decide
  have hdescent : baseEnd_8141591 < baseStart_8141591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141604 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_8141604 : Nat := 118140960795 + 8141604 * 2 ^ 59
def prefixEnd_8141604 : Nat := 4983230072969 + 3 ^ 40 * 8141604 * 2
def baseEnd_8141604 : Nat := 4180556150568069170607451

theorem tailTrace_8141604 : CollatzResearch.WordTrace tailWord_8141604 prefixEnd_8141604 4180556150568069170607451 := by
  unfold tailWord_8141604
  simp only [CollatzResearch.WordTrace]
  refine ⟨148474346598183329053459933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197965795464244438737946577 148474346598183329053459933)
  ·
    refine ⟨55677879974318748395047475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148474346598183329053459933 55677879974318748395047475)
    ·
      refine ⟨83516819961478122592571213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55677879974318748395047475 83516819961478122592571213)
      ·
        refine ⟨31318807485554295972214205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83516819961478122592571213 31318807485554295972214205)
        ·
          refine ⟨11744552807082860989580327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31318807485554295972214205 11744552807082860989580327)
          ·
            refine ⟨17616829210624291484370491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744552807082860989580327 17616829210624291484370491)
            ·
              refine ⟨26425243815936437226555737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17616829210624291484370491 26425243815936437226555737)
              ·
                refine ⟨19818932861952327919916803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26425243815936437226555737 19818932861952327919916803)
                ·
                  refine ⟨29728399292928491879875205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19818932861952327919916803 29728399292928491879875205)
                  ·
                    refine ⟨5574074867424092227476601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29728399292928491879875205 5574074867424092227476601)
                    ·
                      refine ⟨4180556150568069170607451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574074867424092227476601 4180556150568069170607451)
                      ·
                        rfl

theorem cell23_8141604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_8141604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141604 prefixEnd_8141604 := by exact prefixLift 8141604
  have htrace : WordTrace (prefixWord ++ tailWord_8141604) baseStart_8141604 baseEnd_8141604 := by
    simpa [prefixWord, tailWord_8141604, baseEnd_8141604] using wordTrace_append hprefix tailTrace_8141604
  have hstable : (prefixWord ++ tailWord_8141604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141604).length < 2 ^ (prefixWord ++ tailWord_8141604).sum := by decide
  have hdescent : baseEnd_8141604 < baseStart_8141604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141621 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_8141621 : Nat := 118140960795 + 8141621 * 2 ^ 59
def prefixEnd_8141621 : Nat := 4983230072969 + 3 ^ 40 * 8141621 * 2
def baseEnd_8141621 : Nat := 4180564879739195604094873

theorem tailTrace_8141621 : CollatzResearch.WordTrace tailWord_8141621 prefixEnd_8141621 4180564879739195604094873 := by
  unfold tailWord_8141621
  simp only [CollatzResearch.WordTrace]
  refine ⟨296949313237305070010288717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197966208824870046673525811 296949313237305070010288717)
  ·
    refine ⟨111355992463989401253858269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296949313237305070010288717 111355992463989401253858269)
    ·
      refine ⟨41758497173996025470196851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111355992463989401253858269 41758497173996025470196851)
      ·
        refine ⟨62637745760994038205295277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41758497173996025470196851 62637745760994038205295277)
        ·
          refine ⟨23489154660372764326985729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62637745760994038205295277 23489154660372764326985729)
          ·
            refine ⟨17616865995279573245239297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23489154660372764326985729 17616865995279573245239297)
            ·
              refine ⟨13212649496459679933929473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17616865995279573245239297 13212649496459679933929473)
              ·
                refine ⟨9909487122344759950447105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13212649496459679933929473 9909487122344759950447105)
                ·
                  refine ⟨7432115341758569962835329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9909487122344759950447105 7432115341758569962835329)
                  ·
                    refine ⟨5574086506318927472126497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7432115341758569962835329 5574086506318927472126497)
                    ·
                      refine ⟨4180564879739195604094873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574086506318927472126497 4180564879739195604094873)
                      ·
                        rfl

theorem cell23_8141621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_8141621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141621 prefixEnd_8141621 := by exact prefixLift 8141621
  have htrace : WordTrace (prefixWord ++ tailWord_8141621) baseStart_8141621 baseEnd_8141621 := by
    simpa [prefixWord, tailWord_8141621, baseEnd_8141621] using wordTrace_append hprefix tailTrace_8141621
  have hstable : (prefixWord ++ tailWord_8141621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141621).length < 2 ^ (prefixWord ++ tailWord_8141621).sum := by decide
  have hdescent : baseEnd_8141621 < baseStart_8141621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141638 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_8141638 : Nat := 118140960795 + 8141638 * 2 ^ 59
def prefixEnd_8141638 : Nat := 4983230072969 + 3 ^ 40 * 8141638 * 2
def baseEnd_8141638 : Nat := 4180573608910322037582295

theorem tailTrace_8141638 : CollatzResearch.WordTrace tailWord_8141638 prefixEnd_8141638 4180573608910322037582295 := by
  unfold tailWord_8141638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279685414945108809801799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197966622185495654609105045 9279685414945108809801799)
  ·
    refine ⟨13919528122417663214702699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9279685414945108809801799 13919528122417663214702699)
    ·
      refine ⟨20879292183626494822054049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919528122417663214702699 20879292183626494822054049)
      ·
        refine ⟨15659469137719871116540537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20879292183626494822054049 15659469137719871116540537)
        ·
          refine ⟨11744601853289903337405403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15659469137719871116540537 11744601853289903337405403)
          ·
            refine ⟨17616902779934855006108105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744601853289903337405403 17616902779934855006108105)
            ·
              refine ⟨13212677084951141254581079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17616902779934855006108105 13212677084951141254581079)
              ·
                refine ⟨19819015627426711881871619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212677084951141254581079 19819015627426711881871619)
                ·
                  refine ⟨29728523441140067822807429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19819015627426711881871619 29728523441140067822807429)
                  ·
                    refine ⟨5574098145213762716776393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29728523441140067822807429 5574098145213762716776393)
                    ·
                      refine ⟨4180573608910322037582295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574098145213762716776393 4180573608910322037582295)
                      ·
                        rfl

theorem cell23_8141638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_8141638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141638 prefixEnd_8141638 := by exact prefixLift 8141638
  have htrace : WordTrace (prefixWord ++ tailWord_8141638) baseStart_8141638 baseEnd_8141638 := by
    simpa [prefixWord, tailWord_8141638, baseEnd_8141638] using wordTrace_append hprefix tailTrace_8141638
  have hstable : (prefixWord ++ tailWord_8141638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141638).length < 2 ^ (prefixWord ++ tailWord_8141638).sum := by decide
  have hdescent : baseEnd_8141638 < baseStart_8141638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141657 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 2, 5]
def baseStart_8141657 : Nat := 118140960795 + 8141657 * 2 ^ 59
def prefixEnd_8141657 : Nat := 4983230072969 + 3 ^ 40 * 8141657 * 2
def baseEnd_8141657 : Nat := 1393527788347585821081569

theorem tailTrace_8141657 : CollatzResearch.WordTrace tailWord_8141657 prefixEnd_8141657 1393527788347585821081569 := by
  unfold tailWord_8141657
  simp only [CollatzResearch.WordTrace]
  refine ⟨296950626265174648158599225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197967084176783098772399483 296950626265174648158599225)
  ·
    refine ⟨222712969698880986118949419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296950626265174648158599225 222712969698880986118949419)
    ·
      refine ⟨334069454548321479178424129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222712969698880986118949419 334069454548321479178424129)
      ·
        refine ⟨250552090911241109383818097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334069454548321479178424129 250552090911241109383818097)
        ·
          refine ⟨187914068183430832037863573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250552090911241109383818097 187914068183430832037863573)
          ·
            refine ⟨8808471946098320251774855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187914068183430832037863573 8808471946098320251774855)
            ·
              refine ⟨13212707919147480377662283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808471946098320251774855 13212707919147480377662283)
              ·
                refine ⟨19819061878721220566493425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212707919147480377662283 19819061878721220566493425)
                ·
                  refine ⟨14864296409040915424870069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19819061878721220566493425 14864296409040915424870069)
                  ·
                    refine ⟨1393527788347585821081569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14864296409040915424870069 1393527788347585821081569)
                    ·
                      rfl

theorem cell23_8141657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_8141657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141657 prefixEnd_8141657 := by exact prefixLift 8141657
  have htrace : WordTrace (prefixWord ++ tailWord_8141657) baseStart_8141657 baseEnd_8141657 := by
    simpa [prefixWord, tailWord_8141657, baseEnd_8141657] using wordTrace_append hprefix tailTrace_8141657
  have hstable : (prefixWord ++ tailWord_8141657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141657).length < 2 ^ (prefixWord ++ tailWord_8141657).sum := by decide
  have hdescent : baseEnd_8141657 < baseStart_8141657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141767 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_8141767 : Nat := 118140960795 + 8141767 * 2 ^ 59
def prefixEnd_8141767 : Nat := 4983230072969 + 3 ^ 40 * 8141767 * 2
def baseEnd_8141767 : Nat := 4180639847914752032869201

theorem tailTrace_8141767 : CollatzResearch.WordTrace tailWord_8141767 prefixEnd_8141767 4180639847914752032869201 := by
  unfold tailWord_8141767
  simp only [CollatzResearch.WordTrace]
  refine ⟨296954638294776136945103555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197969758863184091296735703 296954638294776136945103555)
  ·
    refine ⟨445431957442164205417655333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296954638294776136945103555 445431957442164205417655333)
    ·
      refine ⟨83518492020405788515810375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445431957442164205417655333 83518492020405788515810375)
      ·
        refine ⟨125277738030608682773715563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83518492020405788515810375 125277738030608682773715563)
        ·
          refine ⟨187916607045913024160573345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125277738030608682773715563 187916607045913024160573345)
          ·
            refine ⟨140937455284434768120430009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187916607045913024160573345 140937455284434768120430009)
            ·
              refine ⟨105703091463326076090322507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140937455284434768120430009 105703091463326076090322507)
              ·
                refine ⟨158554637194989114135483761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105703091463326076090322507 158554637194989114135483761)
                ·
                  refine ⟨118915977896241835601612821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158554637194989114135483761 118915977896241835601612821)
                  ·
                    refine ⟨5574186463886336043825601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118915977896241835601612821 5574186463886336043825601)
                    ·
                      refine ⟨4180639847914752032869201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574186463886336043825601 4180639847914752032869201)
                      ·
                        rfl

theorem cell23_8141767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_8141767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141767 prefixEnd_8141767 := by exact prefixLift 8141767
  have htrace : WordTrace (prefixWord ++ tailWord_8141767) baseStart_8141767 baseEnd_8141767 := by
    simpa [prefixWord, tailWord_8141767, baseEnd_8141767] using wordTrace_append hprefix tailTrace_8141767
  have hstable : (prefixWord ++ tailWord_8141767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141767).length < 2 ^ (prefixWord ++ tailWord_8141767).sum := by decide
  have hdescent : baseEnd_8141767 < baseStart_8141767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141781 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_8141781 : Nat := 118140960795 + 8141781 * 2 ^ 59
def prefixEnd_8141781 : Nat := 4983230072969 + 3 ^ 40 * 8141781 * 2
def baseEnd_8141781 : Nat := 1393549012214638326031379

theorem tailTrace_8141781 : CollatzResearch.WordTrace tailWord_8141781 prefixEnd_8141781 1393549012214638326031379 := by
  unfold tailWord_8141781
  simp only [CollatzResearch.WordTrace]
  refine ⟨296955148916725417336113197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197970099277816944890742131 296955148916725417336113197)
  ·
    refine ⟨111358180843772031501042449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296955148916725417336113197 111358180843772031501042449)
    ·
      refine ⟨83518635632829023625781837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111358180843772031501042449 83518635632829023625781837)
      ·
        refine ⟨31319488362310883859668189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83518635632829023625781837 31319488362310883859668189)
        ·
          refine ⟨11744808135866581447375571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31319488362310883859668189 11744808135866581447375571)
          ·
            refine ⟨17617212203799872171063357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744808135866581447375571 17617212203799872171063357)
            ·
              refine ⟨6606454576424952064148759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17617212203799872171063357 6606454576424952064148759)
              ·
                refine ⟨9909681864637428096223139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606454576424952064148759 9909681864637428096223139)
                ·
                  refine ⟨14864522796956142144334709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909681864637428096223139 14864522796956142144334709)
                  ·
                    refine ⟨1393549012214638326031379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14864522796956142144334709 1393549012214638326031379)
                    ·
                      rfl

theorem cell23_8141781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_8141781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141781 prefixEnd_8141781 := by exact prefixLift 8141781
  have htrace : WordTrace (prefixWord ++ tailWord_8141781) baseStart_8141781 baseEnd_8141781 := by
    simpa [prefixWord, tailWord_8141781, baseEnd_8141781] using wordTrace_append hprefix tailTrace_8141781
  have hstable : (prefixWord ++ tailWord_8141781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141781).length < 2 ^ (prefixWord ++ tailWord_8141781).sum := by decide
  have hdescent : baseEnd_8141781 < baseStart_8141781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141807 : List Nat := [1, 1, 2, 1, 4, 5, 1, 8]
def baseStart_8141807 : Nat := 118140960795 + 8141807 * 2 ^ 59
def prefixEnd_8141807 : Nat := 4983230072969 + 3 ^ 40 * 8141807 * 2
def baseEnd_8141807 : Nat := 154839273597812291717371

theorem tailTrace_8141807 : CollatzResearch.WordTrace tailWord_8141807 prefixEnd_8141807 154839273597812291717371 := by
  unfold tailWord_8141807
  simp only [CollatzResearch.WordTrace]
  refine ⟨296956097214631223776559675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197970731476420815851039783 296956097214631223776559675)
  ·
    refine ⟨445434145821946835664839513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296956097214631223776559675 445434145821946835664839513)
    ·
      refine ⟨334075609366460126748629635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445434145821946835664839513 334075609366460126748629635)
      ·
        refine ⟨501113414049690190122944453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334075609366460126748629635 501113414049690190122944453)
        ·
          refine ⟨93958765134316910648052085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501113414049690190122944453 93958765134316910648052085)
          ·
            refine ⟨8808634231342210373254883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93958765134316910648052085 8808634231342210373254883)
            ·
              refine ⟨13212951347013315559882325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808634231342210373254883 13212951347013315559882325)
              ·
                refine ⟨154839273597812291717371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13212951347013315559882325 154839273597812291717371)
                ·
                  rfl

theorem cell23_8141807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 8].length) (baseStart_8141807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141807 prefixEnd_8141807 := by exact prefixLift 8141807
  have htrace : WordTrace (prefixWord ++ tailWord_8141807) baseStart_8141807 baseEnd_8141807 := by
    simpa [prefixWord, tailWord_8141807, baseEnd_8141807] using wordTrace_append hprefix tailTrace_8141807
  have hstable : (prefixWord ++ tailWord_8141807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141807).length < 2 ^ (prefixWord ++ tailWord_8141807).sum := by decide
  have hdescent : baseEnd_8141807 < baseStart_8141807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141812 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_8141812 : Nat := 118140960795 + 8141812 * 2 ^ 59
def prefixEnd_8141812 : Nat := 4983230072969 + 3 ^ 40 * 8141812 * 2
def baseEnd_8141812 : Nat := 4180662954544204356806495

theorem tailTrace_8141812 : CollatzResearch.WordTrace tailWord_8141812 prefixEnd_8141812 4180662954544204356806495 := by
  unfold tailWord_8141812
  simp only [CollatzResearch.WordTrace]
  refine ⟨148478139789806554815245845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197970853053075406420327793 148478139789806554815245845)
  ·
    refine ⟨6959912802647182256964649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148478139789806554815245845 6959912802647182256964649)
    ·
      refine ⟨5219934601985386692723487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6959912802647182256964649 5219934601985386692723487)
      ·
        refine ⟨7829901902978080039085231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219934601985386692723487 7829901902978080039085231)
        ·
          refine ⟨11744852854467120058627847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829901902978080039085231 11744852854467120058627847)
          ·
            refine ⟨17617279281700680087941771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744852854467120058627847 17617279281700680087941771)
            ·
              refine ⟨26425918922551020131912657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17617279281700680087941771 26425918922551020131912657)
              ·
                refine ⟨19819439191913265098934493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26425918922551020131912657 19819439191913265098934493)
                ·
                  refine ⟨7432289696967474412100435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19819439191913265098934493 7432289696967474412100435)
                  ·
                    refine ⟨11148434545451211618150653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7432289696967474412100435 11148434545451211618150653)
                    ·
                      refine ⟨4180662954544204356806495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148434545451211618150653 4180662954544204356806495)
                      ·
                        rfl

theorem cell23_8141812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_8141812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141812 prefixEnd_8141812 := by exact prefixLift 8141812
  have htrace : WordTrace (prefixWord ++ tailWord_8141812) baseStart_8141812 baseEnd_8141812 := by
    simpa [prefixWord, tailWord_8141812, baseEnd_8141812] using wordTrace_append hprefix tailTrace_8141812
  have hstable : (prefixWord ++ tailWord_8141812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141812).length < 2 ^ (prefixWord ++ tailWord_8141812).sum := by decide
  have hdescent : baseEnd_8141812 < baseStart_8141812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141814 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_8141814 : Nat := 118140960795 + 8141814 * 2 ^ 59
def prefixEnd_8141814 : Nat := 4983230072969 + 3 ^ 40 * 8141814 * 2
def baseEnd_8141814 : Nat := 4180663981505513348981485

theorem tailTrace_8141814 : CollatzResearch.WordTrace tailWord_8141814 prefixEnd_8141814 4180663981505513348981485 := by
  unfold tailWord_8141814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559772032850366498254031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197970901683737242648042997 18559772032850366498254031)
  ·
    refine ⟨27839658049275549747381047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18559772032850366498254031 27839658049275549747381047)
    ·
      refine ⟨41759487073913324621071571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27839658049275549747381047 41759487073913324621071571)
      ·
        refine ⟨62639230610869986931607357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41759487073913324621071571 62639230610869986931607357)
        ·
          refine ⟨23489711479076245099352759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62639230610869986931607357 23489711479076245099352759)
          ·
            refine ⟨35234567218614367649029139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23489711479076245099352759 35234567218614367649029139)
            ·
              refine ⟨52851850827921551473543709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35234567218614367649029139 52851850827921551473543709)
              ·
                refine ⟨19819444060470581802578891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52851850827921551473543709 19819444060470581802578891)
                ·
                  refine ⟨29729166090705872703868337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19819444060470581802578891 29729166090705872703868337)
                  ·
                    refine ⟨22296874568029404527901253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29729166090705872703868337 22296874568029404527901253)
                    ·
                      refine ⟨4180663981505513348981485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22296874568029404527901253 4180663981505513348981485)
                      ·
                        rfl

theorem cell23_8141814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_8141814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141814 prefixEnd_8141814 := by exact prefixLift 8141814
  have htrace : WordTrace (prefixWord ++ tailWord_8141814) baseStart_8141814 baseEnd_8141814 := by
    simpa [prefixWord, tailWord_8141814, baseEnd_8141814] using wordTrace_append hprefix tailTrace_8141814
  have hstable : (prefixWord ++ tailWord_8141814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141814).length < 2 ^ (prefixWord ++ tailWord_8141814).sum := by decide
  have hdescent : baseEnd_8141814 < baseStart_8141814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141834 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_8141834 : Nat := 118140960795 + 8141834 * 2 ^ 59
def prefixEnd_8141834 : Nat := 4983230072969 + 3 ^ 40 * 8141834 * 2
def baseEnd_8141834 : Nat := 4180674251118603270731393

theorem tailTrace_8141834 : CollatzResearch.WordTrace tailWord_8141834 prefixEnd_8141834 4180674251118603270731393 := by
  unfold tailWord_8141834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74239270496383351846948139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197971387990355604925195037 74239270496383351846948139)
  ·
    refine ⟨111358905744575027770422209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74239270496383351846948139 111358905744575027770422209)
    ·
      refine ⟨83519179308431270827816657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111358905744575027770422209 83519179308431270827816657)
      ·
        refine ⟨62639384481323453120862493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83519179308431270827816657 62639384481323453120862493)
        ·
          refine ⟨23489769180496294920323435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62639384481323453120862493 23489769180496294920323435)
          ·
            refine ⟨35234653770744442380485153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23489769180496294920323435 35234653770744442380485153)
            ·
              refine ⟨26425990328058331785363865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35234653770744442380485153 26425990328058331785363865)
              ·
                refine ⟨19819492746043748839022899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26425990328058331785363865 19819492746043748839022899)
                ·
                  refine ⟨29729239119065623258534349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19819492746043748839022899 29729239119065623258534349)
                  ·
                    refine ⟨11148464669649608721950381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29729239119065623258534349 11148464669649608721950381)
                    ·
                      refine ⟨4180674251118603270731393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148464669649608721950381 4180674251118603270731393)
                      ·
                        rfl

theorem cell23_8141834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_8141834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141834 prefixEnd_8141834 := by exact prefixLift 8141834
  have htrace : WordTrace (prefixWord ++ tailWord_8141834) baseStart_8141834 baseEnd_8141834 := by
    simpa [prefixWord, tailWord_8141834, baseEnd_8141834] using wordTrace_append hprefix tailTrace_8141834
  have hstable : (prefixWord ++ tailWord_8141834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141834).length < 2 ^ (prefixWord ++ tailWord_8141834).sum := by decide
  have hdescent : baseEnd_8141834 < baseStart_8141834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141838 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_8141838 : Nat := 118140960795 + 8141838 * 2 ^ 59
def prefixEnd_8141838 : Nat := 4983230072969 + 3 ^ 40 * 8141838 * 2
def baseEnd_8141838 : Nat := 4180676305041221255081375

theorem tailTrace_8141838 : CollatzResearch.WordTrace tailWord_8141838 prefixEnd_8141838 4180676305041221255081375 := by
  unfold tailWord_8141838
  simp only [CollatzResearch.WordTrace]
  refine ⟨37119653484689864508867271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197971485251679277380625445 37119653484689864508867271)
  ·
    refine ⟨55679480227034796763300907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37119653484689864508867271 55679480227034796763300907)
    ·
      refine ⟨83519220340552195144951361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55679480227034796763300907 83519220340552195144951361)
      ·
        refine ⟨62639415255414146358713521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83519220340552195144951361 62639415255414146358713521)
        ·
          refine ⟨46979561441560609769035141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62639415255414146358713521 46979561441560609769035141)
          ·
            refine ⟨8808667770292614331694089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46979561441560609769035141 8808667770292614331694089)
            ·
              refine ⟨6606500827719460748770567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8808667770292614331694089 6606500827719460748770567)
              ·
                refine ⟨9909751241579191123155851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606500827719460748770567 9909751241579191123155851)
                ·
                  refine ⟨14864626862368786684733777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909751241579191123155851 14864626862368786684733777)
                  ·
                    refine ⟨11148470146776590013550333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14864626862368786684733777 11148470146776590013550333)
                    ·
                      refine ⟨4180676305041221255081375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148470146776590013550333 4180676305041221255081375)
                      ·
                        rfl

theorem cell23_8141838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_8141838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141838 prefixEnd_8141838 := by exact prefixLift 8141838
  have htrace : WordTrace (prefixWord ++ tailWord_8141838) baseStart_8141838 baseEnd_8141838 := by
    simpa [prefixWord, tailWord_8141838, baseEnd_8141838] using wordTrace_append hprefix tailTrace_8141838
  have hstable : (prefixWord ++ tailWord_8141838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141838).length < 2 ^ (prefixWord ++ tailWord_8141838).sum := by decide
  have hdescent : baseEnd_8141838 < baseStart_8141838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141877 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_8141877 : Nat := 118140960795 + 8141877 * 2 ^ 59
def prefixEnd_8141877 : Nat := 4983230072969 + 3 ^ 40 * 8141877 * 2
def baseEnd_8141877 : Nat := 4180696330786746602493695

theorem tailTrace_8141877 : CollatzResearch.WordTrace tailWord_8141877 prefixEnd_8141877 4180696330786746602493695 := by
  unfold tailWord_8141877
  simp only [CollatzResearch.WordTrace]
  refine ⟨296958650324377625731607885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197972433549585083821071923 296958650324377625731607885)
  ·
    refine ⟨111359493871641609649352957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296958650324377625731607885 111359493871641609649352957)
    ·
      refine ⟨41759810201865603618507359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111359493871641609649352957 41759810201865603618507359)
      ·
        refine ⟨62639715302798405427761039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41759810201865603618507359 62639715302798405427761039)
        ·
          refine ⟨93959572954197608141641559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62639715302798405427761039 93959572954197608141641559)
          ·
            refine ⟨140939359431296412212462339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93959572954197608141641559 140939359431296412212462339)
            ·
              refine ⟨211409039146944618318693509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140939359431296412212462339 211409039146944618318693509)
              ·
                refine ⟨39639194840052115934755033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211409039146944618318693509 39639194840052115934755033)
                ·
                  refine ⟨29729396130039086951066275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39639194840052115934755033 29729396130039086951066275)
                  ·
                    refine ⟨44594094195058630426599413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29729396130039086951066275 44594094195058630426599413)
                    ·
                      refine ⟨4180696330786746602493695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44594094195058630426599413 4180696330786746602493695)
                      ·
                        rfl

theorem cell23_8141877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_8141877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141877 prefixEnd_8141877 := by exact prefixLift 8141877
  have htrace : WordTrace (prefixWord ++ tailWord_8141877) baseStart_8141877 baseEnd_8141877 := by
    simpa [prefixWord, tailWord_8141877, baseEnd_8141877] using wordTrace_append hprefix tailTrace_8141877
  have hstable : (prefixWord ++ tailWord_8141877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141877).length < 2 ^ (prefixWord ++ tailWord_8141877).sum := by decide
  have hdescent : baseEnd_8141877 < baseStart_8141877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141878 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_8141878 : Nat := 118140960795 + 8141878 * 2 ^ 59
def prefixEnd_8141878 : Nat := 4983230072969 + 3 ^ 40 * 8141878 * 2
def baseEnd_8141878 : Nat := 4180696844267401098581191

theorem tailTrace_8141878 : CollatzResearch.WordTrace tailWord_8141878 prefixEnd_8141878 4180696844267401098581191 := by
  unfold tailWord_8141878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559917924835875181399643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197972457864916001934929525 18559917924835875181399643)
  ·
    refine ⟨27839876887253812772099465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18559917924835875181399643 27839876887253812772099465)
    ·
      refine ⟨20879907665440359579074599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27839876887253812772099465 20879907665440359579074599)
      ·
        refine ⟨31319861498160539368611899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20879907665440359579074599 31319861498160539368611899)
        ·
          refine ⟨46979792247240809052917849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31319861498160539368611899 46979792247240809052917849)
          ·
            refine ⟨35234844185430606789688387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46979792247240809052917849 35234844185430606789688387)
            ·
              refine ⟨52852266278145910184532581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35234844185430606789688387 52852266278145910184532581)
              ·
                refine ⟨9909799927152358159599859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52852266278145910184532581 9909799927152358159599859)
                ·
                  refine ⟨14864699890728537239399789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909799927152358159599859 14864699890728537239399789)
                  ·
                    refine ⟨5574262459023201464774921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14864699890728537239399789 5574262459023201464774921)
                    ·
                      refine ⟨4180696844267401098581191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574262459023201464774921 4180696844267401098581191)
                      ·
                        rfl

theorem cell23_8141878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_8141878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141878 prefixEnd_8141878 := by exact prefixLift 8141878
  have htrace : WordTrace (prefixWord ++ tailWord_8141878) baseStart_8141878 baseEnd_8141878 := by
    simpa [prefixWord, tailWord_8141878, baseEnd_8141878] using wordTrace_append hprefix tailTrace_8141878
  have hstable : (prefixWord ++ tailWord_8141878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141878).length < 2 ^ (prefixWord ++ tailWord_8141878).sum := by decide
  have hdescent : baseEnd_8141878 < baseStart_8141878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141947 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4]
def baseStart_8141947 : Nat := 118140960795 + 8141947 * 2 ^ 59
def prefixEnd_8141947 : Nat := 4983230072969 + 3 ^ 40 * 8141947 * 2
def baseEnd_8141947 : Nat := 4180732274432561328618373

theorem tailTrace_8141947 : CollatzResearch.WordTrace tailWord_8141947 prefixEnd_8141947 4180732274432561328618373 := by
  unfold tailWord_8141947
  simp only [CollatzResearch.WordTrace]
  refine ⟨296961203434124027686656095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197974135622749351791104063 296961203434124027686656095)
  ·
    refine ⟨445441805151186041529984143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296961203434124027686656095 445441805151186041529984143)
    ·
      refine ⟨668162707726779062294976215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445441805151186041529984143 668162707726779062294976215)
      ·
        refine ⟨1002244061590168593442464323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668162707726779062294976215 1002244061590168593442464323)
        ·
          refine ⟨1503366092385252890163696485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002244061590168593442464323 1503366092385252890163696485)
          ·
            refine ⟨281881142322234916905693091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1503366092385252890163696485 281881142322234916905693091)
            ·
              refine ⟨422821713483352375358539637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281881142322234916905693091 422821713483352375358539637)
              ·
                refine ⟨39639535639064285189863091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422821713483352375358539637 39639535639064285189863091)
                ·
                  refine ⟨59459303458596427784794637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39639535639064285189863091 59459303458596427784794637)
                  ·
                    refine ⟨22297238796973660419297989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59459303458596427784794637 22297238796973660419297989)
                    ·
                      refine ⟨4180732274432561328618373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22297238796973660419297989 4180732274432561328618373)
                      ·
                        rfl

theorem cell23_8141947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_8141947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141947 prefixEnd_8141947 := by exact prefixLift 8141947
  have htrace : WordTrace (prefixWord ++ tailWord_8141947) baseStart_8141947 baseEnd_8141947 := by
    simpa [prefixWord, tailWord_8141947, baseEnd_8141947] using wordTrace_append hprefix tailTrace_8141947
  have hstable : (prefixWord ++ tailWord_8141947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141947).length < 2 ^ (prefixWord ++ tailWord_8141947).sum := by decide
  have hdescent : baseEnd_8141947 < baseStart_8141947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141964 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 6, 2]
def baseStart_8141964 : Nat := 118140960795 + 8141964 * 2 ^ 59
def prefixEnd_8141964 : Nat := 4983230072969 + 3 ^ 40 * 8141964 * 2
def baseEnd_8141964 : Nat := 4180741003603687762105795

theorem tailTrace_8141964 : CollatzResearch.WordTrace tailWord_8141964 prefixEnd_8141964 4180741003603687762105795 := by
  unfold tailWord_8141964
  simp only [CollatzResearch.WordTrace]
  refine ⟨148480911737531219795012473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197974548983374959726683297 148480911737531219795012473)
  ·
    refine ⟨111360683803148414846259355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148480911737531219795012473 111360683803148414846259355)
    ·
      refine ⟨167041025704722622269389033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111360683803148414846259355 167041025704722622269389033)
      ·
        refine ⟨125280769278541966702041775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167041025704722622269389033 125280769278541966702041775)
        ·
          refine ⟨187921153917812950053062663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125280769278541966702041775 187921153917812950053062663)
          ·
            refine ⟨281881730876719425079593995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187921153917812950053062663 281881730876719425079593995)
            ·
              refine ⟨422822596315079137619390993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281881730876719425079593995 422822596315079137619390993)
              ·
                refine ⟨317116947236309353214543245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422822596315079137619390993 317116947236309353214543245)
                ·
                  refine ⟨118918855213616007455453717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317116947236309353214543245 118918855213616007455453717)
                  ·
                    refine ⟨5574321338138250349474393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118918855213616007455453717 5574321338138250349474393)
                    ·
                      refine ⟨4180741003603687762105795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574321338138250349474393 4180741003603687762105795)
                      ·
                        rfl

theorem cell23_8141964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_8141964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141964 prefixEnd_8141964 := by exact prefixLift 8141964
  have htrace : WordTrace (prefixWord ++ tailWord_8141964) baseStart_8141964 baseEnd_8141964 := by
    simpa [prefixWord, tailWord_8141964, baseEnd_8141964] using wordTrace_append hprefix tailTrace_8141964
  have hstable : (prefixWord ++ tailWord_8141964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141964).length < 2 ^ (prefixWord ++ tailWord_8141964).sum := by decide
  have hdescent : baseEnd_8141964 < baseStart_8141964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141977 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_8141977 : Nat := 118140960795 + 8141977 * 2 ^ 59
def prefixEnd_8141977 : Nat := 4983230072969 + 3 ^ 40 * 8141977 * 2
def baseEnd_8141977 : Nat := 4180747678852196211243235

theorem tailTrace_8141977 : CollatzResearch.WordTrace tailWord_8141977 prefixEnd_8141977 4180747678852196211243235 := by
  unfold tailWord_8141977
  simp only [CollatzResearch.WordTrace]
  refine ⟨296962297624015342810248185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197974865082676895206832123 296962297624015342810248185)
  ·
    refine ⟨222721723218011507107686139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296962297624015342810248185 222721723218011507107686139)
    ·
      refine ⟨334082584827017260661529209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222721723218011507107686139 334082584827017260661529209)
      ·
        refine ⟨250561938620262945496146907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334082584827017260661529209 250561938620262945496146907)
        ·
          refine ⟨375842907930394418244220361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250561938620262945496146907 375842907930394418244220361)
          ·
            refine ⟨281882180947795813683165271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375842907930394418244220361 281882180947795813683165271)
            ·
              refine ⟨422823271421693720524747907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281882180947795813683165271 422823271421693720524747907)
              ·
                refine ⟨634234907132540580787121861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422823271421693720524747907 634234907132540580787121861)
                ·
                  refine ⟨118919045087351358897585349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634234907132540580787121861 118919045087351358897585349)
                  ·
                    refine ⟨22297320953878379793297253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118919045087351358897585349 22297320953878379793297253)
                    ·
                      refine ⟨4180747678852196211243235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22297320953878379793297253 4180747678852196211243235)
                      ·
                        rfl

theorem cell23_8141977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_8141977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141977 prefixEnd_8141977 := by exact prefixLift 8141977
  have htrace : WordTrace (prefixWord ++ tailWord_8141977) baseStart_8141977 baseEnd_8141977 := by
    simpa [prefixWord, tailWord_8141977, baseEnd_8141977] using wordTrace_append hprefix tailTrace_8141977
  have hstable : (prefixWord ++ tailWord_8141977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141977).length < 2 ^ (prefixWord ++ tailWord_8141977).sum := by decide
  have hdescent : baseEnd_8141977 < baseStart_8141977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141981 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_8141981 : Nat := 118140960795 + 8141981 * 2 ^ 59
def prefixEnd_8141981 : Nat := 4983230072969 + 3 ^ 40 * 8141981 * 2
def baseEnd_8141981 : Nat := 4180749732774814195593217

theorem tailTrace_8141981 : CollatzResearch.WordTrace tailWord_8141981 prefixEnd_8141981 4180749732774814195593217 := by
  unfold tailWord_8141981
  simp only [CollatzResearch.WordTrace]
  refine ⟨296962443516000851493393797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197974962344000567662262531 296962443516000851493393797)
  ·
    refine ⟨55680458159250159655011337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296962443516000851493393797 55680458159250159655011337)
    ·
      refine ⟨41760343619437619741258503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55680458159250159655011337 41760343619437619741258503)
      ·
        refine ⟨62640515429156429611887755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41760343619437619741258503 62640515429156429611887755)
        ·
          refine ⟨93960773143734644417831633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62640515429156429611887755 93960773143734644417831633)
          ·
            refine ⟨70470579857800983313373725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93960773143734644417831633 70470579857800983313373725)
            ·
              refine ⟨26426467446675368742515147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70470579857800983313373725 26426467446675368742515147)
              ·
                refine ⟨39639701170013053113772721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26426467446675368742515147 39639701170013053113772721)
                ·
                  refine ⟨29729775877509789835329541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39639701170013053113772721 29729775877509789835329541)
                  ·
                    refine ⟨5574332977033085594124289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29729775877509789835329541 5574332977033085594124289)
                    ·
                      refine ⟨4180749732774814195593217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574332977033085594124289 4180749732774814195593217)
                      ·
                        rfl

theorem cell23_8141981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_8141981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141981 prefixEnd_8141981 := by exact prefixLift 8141981
  have htrace : WordTrace (prefixWord ++ tailWord_8141981) baseStart_8141981 baseEnd_8141981 := by
    simpa [prefixWord, tailWord_8141981, baseEnd_8141981] using wordTrace_append hprefix tailTrace_8141981
  have hstable : (prefixWord ++ tailWord_8141981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141981).length < 2 ^ (prefixWord ++ tailWord_8141981).sum := by decide
  have hdescent : baseEnd_8141981 < baseStart_8141981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141984 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_8141984 : Nat := 118140960795 + 8141984 * 2 ^ 59
def prefixEnd_8141984 : Nat := 4983230072969 + 3 ^ 40 * 8141984 * 2
def baseEnd_8141984 : Nat := 4180751273216777683855703

theorem tailTrace_8141984 : CollatzResearch.WordTrace tailWord_8141984 prefixEnd_8141984 4180751273216777683855703 := by
  unfold tailWord_8141984
  simp only [CollatzResearch.WordTrace]
  refine ⟨148481276467494991502876503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197975035289993322003835337 148481276467494991502876503)
  ·
    refine ⟨222721914701242487254314755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148481276467494991502876503 222721914701242487254314755)
    ·
      refine ⟨334082872051863730881472133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222721914701242487254314755 334082872051863730881472133)
      ·
        refine ⟨62640538509724449540276025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334082872051863730881472133 62640538509724449540276025)
        ·
          refine ⟨46980403882293337155207019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62640538509724449540276025 46980403882293337155207019)
          ·
            refine ⟨70470605823440005732810529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46980403882293337155207019 70470605823440005732810529)
            ·
              refine ⟨52852954367580004299607897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70470605823440005732810529 52852954367580004299607897)
              ·
                refine ⟨39639715775685003224705923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52852954367580004299607897 39639715775685003224705923)
                ·
                  refine ⟨59459573663527504837058885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39639715775685003224705923 59459573663527504837058885)
                  ·
                    refine ⟨11148670061911407156948541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59459573663527504837058885 11148670061911407156948541)
                    ·
                      refine ⟨4180751273216777683855703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148670061911407156948541 4180751273216777683855703)
                      ·
                        rfl

theorem cell23_8141984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_8141984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141984 prefixEnd_8141984 := by exact prefixLift 8141984
  have htrace : WordTrace (prefixWord ++ tailWord_8141984) baseStart_8141984 baseEnd_8141984 := by
    simpa [prefixWord, tailWord_8141984, baseEnd_8141984] using wordTrace_append hprefix tailTrace_8141984
  have hstable : (prefixWord ++ tailWord_8141984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141984).length < 2 ^ (prefixWord ++ tailWord_8141984).sum := by decide
  have hdescent : baseEnd_8141984 < baseStart_8141984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8141991 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 5, 4]
def baseStart_8141991 : Nat := 118140960795 + 8141991 * 2 ^ 59
def prefixEnd_8141991 : Nat := 4983230072969 + 3 ^ 40 * 8141991 * 2
def baseEnd_8141991 : Nat := 1393584955860453052156057

theorem tailTrace_8141991 : CollatzResearch.WordTrace tailWord_8141991 prefixEnd_8141991 1393584955860453052156057 := by
  unfold tailWord_8141991
  simp only [CollatzResearch.WordTrace]
  refine ⟨296962808245964623201257827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197975205497309748800838551 296962808245964623201257827)
  ·
    refine ⟨445444212368946934801886741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296962808245964623201257827 445444212368946934801886741)
    ·
      refine ⟨20880197454794387568838441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 445444212368946934801886741 20880197454794387568838441)
      ·
        refine ⟨15660148091095790676628831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20880197454794387568838441 15660148091095790676628831)
        ·
          refine ⟨23490222136643686014943247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660148091095790676628831 23490222136643686014943247)
          ·
            refine ⟨35235333204965529022414871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23490222136643686014943247 35235333204965529022414871)
            ·
              refine ⟨52852999807448293533622307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35235333204965529022414871 52852999807448293533622307)
              ·
                refine ⟨79279499711172440300433461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52852999807448293533622307 79279499711172440300433461)
                ·
                  refine ⟨7432453097922416278165637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79279499711172440300433461 7432453097922416278165637)
                  ·
                    refine ⟨1393584955860453052156057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7432453097922416278165637 1393584955860453052156057)
                    ·
                      rfl

theorem cell23_8141991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_8141991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8141991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8141991 prefixEnd_8141991 := by exact prefixLift 8141991
  have htrace : WordTrace (prefixWord ++ tailWord_8141991) baseStart_8141991 baseEnd_8141991 := by
    simpa [prefixWord, tailWord_8141991, baseEnd_8141991] using wordTrace_append hprefix tailTrace_8141991
  have hstable : (prefixWord ++ tailWord_8141991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8141991).length < 2 ^ (prefixWord ++ tailWord_8141991).sum := by decide
  have hdescent : baseEnd_8141991 < baseStart_8141991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8141991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142001 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_8142001 : Nat := 118140960795 + 8142001 * 2 ^ 59
def prefixEnd_8142001 : Nat := 4983230072969 + 3 ^ 40 * 8142001 * 2
def baseEnd_8142001 : Nat := 4180760002387904117343125

theorem tailTrace_8142001 : CollatzResearch.WordTrace tailWord_8142001 prefixEnd_8142001 4180760002387904117343125 := by
  unfold tailWord_8142001
  simp only [CollatzResearch.WordTrace]
  refine ⟨296963172975928394909121857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197975448650618929939414571 296963172975928394909121857)
  ·
    refine ⟨222722379731946296181841393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296963172975928394909121857 222722379731946296181841393)
    ·
      refine ⟨167041784798959722136381045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222722379731946296181841393 167041784798959722136381045)
      ·
        refine ⟨15660167324902473950285723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167041784798959722136381045 15660167324902473950285723)
        ·
          refine ⟨23490250987353710925428585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660167324902473950285723 23490250987353710925428585)
          ·
            refine ⟨17617688240515283194071439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23490250987353710925428585 17617688240515283194071439)
            ·
              refine ⟨26426532360772924791107159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17617688240515283194071439 26426532360772924791107159)
              ·
                refine ⟨39639798541159387186660739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26426532360772924791107159 39639798541159387186660739)
                ·
                  refine ⟨59459697811739080779991109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39639798541159387186660739 59459697811739080779991109)
                  ·
                    refine ⟨11148693339701077646248333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59459697811739080779991109 11148693339701077646248333)
                    ·
                      refine ⟨4180760002387904117343125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148693339701077646248333 4180760002387904117343125)
                      ·
                        rfl

theorem cell23_8142001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_8142001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142001 prefixEnd_8142001 := by exact prefixLift 8142001
  have htrace : WordTrace (prefixWord ++ tailWord_8142001) baseStart_8142001 baseEnd_8142001 := by
    simpa [prefixWord, tailWord_8142001, baseEnd_8142001] using wordTrace_append hprefix tailTrace_8142001
  have hstable : (prefixWord ++ tailWord_8142001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142001).length < 2 ^ (prefixWord ++ tailWord_8142001).sum := by decide
  have hdescent : baseEnd_8142001 < baseStart_8142001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142027 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_8142027 : Nat := 118140960795 + 8142027 * 2 ^ 59
def prefixEnd_8142027 : Nat := 4983230072969 + 3 ^ 40 * 8142027 * 2
def baseEnd_8142027 : Nat := 4180773352884921015618005

theorem tailTrace_8142027 : CollatzResearch.WordTrace tailWord_8142027 prefixEnd_8142027 4180773352884921015618005 := by
  unfold tailWord_8142027
  simp only [CollatzResearch.WordTrace]
  refine ⟨296964121273834201349568335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197976080849222800899712223 296964121273834201349568335)
  ·
    refine ⟨445446181910751302024352503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296964121273834201349568335 445446181910751302024352503)
    ·
      refine ⟨668169272866126953036528755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445446181910751302024352503 668169272866126953036528755)
      ·
        refine ⟨1002253909299190429554793133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668169272866126953036528755 1002253909299190429554793133)
        ·
          refine ⟨375845215987196411083047425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002253909299190429554793133 375845215987196411083047425)
          ·
            refine ⟨281883911990397308312285569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375845215987196411083047425 281883911990397308312285569)
            ·
              refine ⟨211412933992797981234214177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281883911990397308312285569 211412933992797981234214177)
              ·
                refine ⟨158559700494598485925660633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211412933992797981234214177 158559700494598485925660633)
                ·
                  refine ⟨118919775370948864444245475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158559700494598485925660633 118919775370948864444245475)
                  ·
                    refine ⟨178379663056423296666368213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118919775370948864444245475 178379663056423296666368213)
                    ·
                      refine ⟨4180773352884921015618005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178379663056423296666368213 4180773352884921015618005)
                      ·
                        rfl

theorem cell23_8142027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_8142027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142027 prefixEnd_8142027 := by exact prefixLift 8142027
  have htrace : WordTrace (prefixWord ++ tailWord_8142027) baseStart_8142027 baseEnd_8142027 := by
    simpa [prefixWord, tailWord_8142027, baseEnd_8142027] using wordTrace_append hprefix tailTrace_8142027
  have hstable : (prefixWord ++ tailWord_8142027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142027).length < 2 ^ (prefixWord ++ tailWord_8142027).sum := by decide
  have hdescent : baseEnd_8142027 < baseStart_8142027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142081 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 4, 4]
def baseStart_8142081 : Nat := 118140960795 + 8142081 * 2 ^ 59
def prefixEnd_8142081 : Nat := 4983230072969 + 3 ^ 40 * 8142081 * 2
def baseEnd_8142081 : Nat := 1393600360280087934780919

theorem tailTrace_8142081 : CollatzResearch.WordTrace tailWord_8142081 prefixEnd_8142081 1393600360280087934780919 := by
  unfold tailWord_8142081
  simp only [CollatzResearch.WordTrace]
  refine ⟨296966090815638568572034097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197977393877092379048022731 296966090815638568572034097)
  ·
    refine ⟨222724568111728926429025573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296966090815638568572034097 222724568111728926429025573)
    ·
      refine ⟨41760856520949173705442295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222724568111728926429025573 41760856520949173705442295)
      ·
        refine ⟨62641284781423760558163443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41760856520949173705442295 62641284781423760558163443)
        ·
          refine ⟨93961927172135640837245165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62641284781423760558163443 93961927172135640837245165)
          ·
            refine ⟨35235722689550865313966937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93961927172135640837245165 35235722689550865313966937)
            ·
              refine ⟨26426792017163148985475203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35235722689550865313966937 26426792017163148985475203)
              ·
                refine ⟨39640188025744723478212805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26426792017163148985475203 39640188025744723478212805)
                ·
                  refine ⟨7432535254827135652164901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39640188025744723478212805 7432535254827135652164901)
                  ·
                    refine ⟨1393600360280087934780919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7432535254827135652164901 1393600360280087934780919)
                    ·
                      rfl

theorem cell23_8142081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_8142081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142081 prefixEnd_8142081 := by exact prefixLift 8142081
  have htrace : WordTrace (prefixWord ++ tailWord_8142081) baseStart_8142081 baseEnd_8142081 := by
    simpa [prefixWord, tailWord_8142081, baseEnd_8142081] using wordTrace_append hprefix tailTrace_8142081
  have hstable : (prefixWord ++ tailWord_8142081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142081).length < 2 ^ (prefixWord ++ tailWord_8142081).sum := by decide
  have hdescent : baseEnd_8142081 < baseStart_8142081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142082 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_8142082 : Nat := 118140960795 + 8142082 * 2 ^ 59
def prefixEnd_8142082 : Nat := 4983230072969 + 3 ^ 40 * 8142082 * 2
def baseEnd_8142082 : Nat := 4180801594320918300430253

theorem tailTrace_8142082 : CollatzResearch.WordTrace tailWord_8142082 prefixEnd_8142082 4180801594320918300430253 := by
  unfold tailWord_8142082
  simp only [CollatzResearch.WordTrace]
  refine ⟨74241531822158736435705125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197977418192423297161880333 74241531822158736435705125)
  ·
    refine ⟨13920287216654763081694711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74241531822158736435705125 13920287216654763081694711)
    ·
      refine ⟨20880430824982144622542067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13920287216654763081694711 20880430824982144622542067)
      ·
        refine ⟨31320646237473216933813101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20880430824982144622542067 31320646237473216933813101)
        ·
          refine ⟨11745242339052456350179913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31320646237473216933813101 11745242339052456350179913)
          ·
            refine ⟨8808931754289342262634935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11745242339052456350179913 8808931754289342262634935)
            ·
              refine ⟨13213397631434013393952403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808931754289342262634935 13213397631434013393952403)
              ·
                refine ⟨19820096447151020090928605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13213397631434013393952403 19820096447151020090928605)
                ·
                  refine ⟨7432536167681632534098227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19820096447151020090928605 7432536167681632534098227)
                  ·
                    refine ⟨11148804251522448801147341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7432536167681632534098227 11148804251522448801147341)
                    ·
                      refine ⟨4180801594320918300430253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148804251522448801147341 4180801594320918300430253)
                      ·
                        rfl

theorem cell23_8142082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_8142082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142082 prefixEnd_8142082 := by exact prefixLift 8142082
  have htrace : WordTrace (prefixWord ++ tailWord_8142082) baseStart_8142082 baseEnd_8142082 := by
    simpa [prefixWord, tailWord_8142082, baseEnd_8142082] using wordTrace_append hprefix tailTrace_8142082
  have hstable : (prefixWord ++ tailWord_8142082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142082).length < 2 ^ (prefixWord ++ tailWord_8142082).sum := by decide
  have hdescent : baseEnd_8142082 < baseStart_8142082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142094 : List Nat := [4, 1, 1, 2, 1, 3, 1, 10]
def baseStart_8142094 : Nat := 118140960795 + 8142094 * 2 ^ 59
def prefixEnd_8142094 : Nat := 4983230072969 + 3 ^ 40 * 8142094 * 2
def baseEnd_8142094 : Nat := 154844731706991564943711

theorem tailTrace_8142094 : CollatzResearch.WordTrace tailWord_8142094 prefixEnd_8142094 154844731706991564943711 := by
  unfold tailWord_8142094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37120820620573933974032167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197977709976394314528171557 37120820620573933974032167)
  ·
    refine ⟨55681230930860900961048251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37120820620573933974032167 55681230930860900961048251)
    ·
      refine ⟨83521846396291351441572377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55681230930860900961048251 83521846396291351441572377)
      ·
        refine ⟨62641384797218513581179283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83521846396291351441572377 62641384797218513581179283)
        ·
          refine ⟨93962077195827770371768925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62641384797218513581179283 93962077195827770371768925)
          ·
            refine ⟨35235778948435413889413347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93962077195827770371768925 35235778948435413889413347)
            ·
              refine ⟨52853668422653120834120021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35235778948435413889413347 52853668422653120834120021)
              ·
                refine ⟨154844731706991564943711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52853668422653120834120021 154844731706991564943711)
                ·
                  rfl

theorem cell23_8142094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_8142094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142094 prefixEnd_8142094 := by exact prefixLift 8142094
  have htrace : WordTrace (prefixWord ++ tailWord_8142094) baseStart_8142094 baseEnd_8142094 := by
    simpa [prefixWord, tailWord_8142094, baseEnd_8142094] using wordTrace_append hprefix tailTrace_8142094
  have hstable : (prefixWord ++ tailWord_8142094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142094).length < 2 ^ (prefixWord ++ tailWord_8142094).sum := by decide
  have hdescent : baseEnd_8142094 < baseStart_8142094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142108 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_8142108 : Nat := 118140960795 + 8142108 * 2 ^ 59
def prefixEnd_8142108 : Nat := 4983230072969 + 3 ^ 40 * 8142108 * 2
def baseEnd_8142108 : Nat := 4180814944817935198705133

theorem tailTrace_8142108 : CollatzResearch.WordTrace tailWord_8142108 prefixEnd_8142108 4180814944817935198705133 := by
  unfold tailWord_8142108
  simp only [CollatzResearch.WordTrace]
  refine ⟨148483537793270376091633489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197978050391027168122177985 148483537793270376091633489)
  ·
    refine ⟨111362653344952782068725117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148483537793270376091633489 111362653344952782068725117)
    ·
      refine ⟨41760995004357293275771919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111362653344952782068725117 41760995004357293275771919)
      ·
        refine ⟨62641492506535939913657879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41760995004357293275771919 62641492506535939913657879)
        ·
          refine ⟨93962238759803909870486819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62641492506535939913657879 93962238759803909870486819)
          ·
            refine ⟨140943358139705864805730229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93962238759803909870486819 140943358139705864805730229)
            ·
              refine ⟨13213439825597424825537209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140943358139705864805730229 13213439825597424825537209)
              ·
                refine ⟨9910079869198068619152907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13213439825597424825537209 9910079869198068619152907)
                ·
                  refine ⟨14865119803797102928729361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910079869198068619152907 14865119803797102928729361)
                  ·
                    refine ⟨11148839852847827196547021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14865119803797102928729361 11148839852847827196547021)
                    ·
                      refine ⟨4180814944817935198705133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148839852847827196547021 4180814944817935198705133)
                      ·
                        rfl

theorem cell23_8142108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_8142108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142108 prefixEnd_8142108 := by exact prefixLift 8142108
  have htrace : WordTrace (prefixWord ++ tailWord_8142108) baseStart_8142108 baseEnd_8142108 := by
    simpa [prefixWord, tailWord_8142108, baseEnd_8142108] using wordTrace_append hprefix tailTrace_8142108
  have hstable : (prefixWord ++ tailWord_8142108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142108).length < 2 ^ (prefixWord ++ tailWord_8142108).sum := by decide
  have hdescent : baseEnd_8142108 < baseStart_8142108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142125 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_8142125 : Nat := 118140960795 + 8142125 * 2 ^ 59
def prefixEnd_8142125 : Nat := 4983230072969 + 3 ^ 40 * 8142125 * 2
def baseEnd_8142125 : Nat := 4180823673989061632192555

theorem tailTrace_8142125 : CollatzResearch.WordTrace tailWord_8142125 prefixEnd_8142125 4180823673989061632192555 := by
  unfold tailWord_8142125
  simp only [CollatzResearch.WordTrace]
  refine ⟨296967695627479164086635829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197978463751652776057757219 296967695627479164086635829)
  ·
    refine ⟨27840721465076171633122109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296967695627479164086635829 27840721465076171633122109)
    ·
      refine ⟨10440270549403564362420791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27840721465076171633122109 10440270549403564362420791)
      ·
        refine ⟨15660405824105346543631187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10440270549403564362420791 15660405824105346543631187)
        ·
          refine ⟨23490608736158019815446781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660405824105346543631187 23490608736158019815446781)
          ·
            refine ⟨8808978276059257430792543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23490608736158019815446781 8808978276059257430792543)
            ·
              refine ⟨13213467414088886146188815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808978276059257430792543 13213467414088886146188815)
              ·
                refine ⟨19820201121133329219283223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13213467414088886146188815 19820201121133329219283223)
                ·
                  refine ⟨29730301681699993828924835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19820201121133329219283223 29730301681699993828924835)
                  ·
                    refine ⟨44595452522549990743387253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29730301681699993828924835 44595452522549990743387253)
                    ·
                      refine ⟨4180823673989061632192555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44595452522549990743387253 4180823673989061632192555)
                      ·
                        rfl

theorem cell23_8142125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_8142125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142125 prefixEnd_8142125 := by exact prefixLift 8142125
  have htrace : WordTrace (prefixWord ++ tailWord_8142125) baseStart_8142125 baseEnd_8142125 := by
    simpa [prefixWord, tailWord_8142125, baseEnd_8142125] using wordTrace_append hprefix tailTrace_8142125
  have hstable : (prefixWord ++ tailWord_8142125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142125).length < 2 ^ (prefixWord ++ tailWord_8142125).sum := by decide
  have hdescent : baseEnd_8142125 < baseStart_8142125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142144 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_8142144 : Nat := 118140960795 + 8142144 * 2 ^ 59
def prefixEnd_8142144 : Nat := 4983230072969 + 3 ^ 40 * 8142144 * 2
def baseEnd_8142144 : Nat := 4180833430121497057854967

theorem tailTrace_8142144 : CollatzResearch.WordTrace tailWord_8142144 prefixEnd_8142144 4180833430121497057854967 := by
  unfold tailWord_8142144
  simp only [CollatzResearch.WordTrace]
  refine ⟨148484194307205165165788743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197978925742940220221051657 148484194307205165165788743)
  ·
    refine ⟨222726291460807747748683115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148484194307205165165788743 222726291460807747748683115)
    ·
      refine ⟨334089437191211621623024673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222726291460807747748683115 334089437191211621623024673)
      ·
        refine ⟨250567077893408716217268505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334089437191211621623024673 250567077893408716217268505)
        ·
          refine ⟨187925308420056537162951379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250567077893408716217268505 187925308420056537162951379)
          ·
            refine ⟨281887962630084805744427069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187925308420056537162951379 281887962630084805744427069)
            ·
              refine ⟨105707985986281802154160151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281887962630084805744427069 105707985986281802154160151)
              ·
                refine ⟨158561978979422703231240227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105707985986281802154160151 158561978979422703231240227)
                ·
                  refine ⟨237842968469134054846860341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158561978979422703231240227 237842968469134054846860341)
                  ·
                    refine ⟨22297778293981317641893157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237842968469134054846860341 22297778293981317641893157)
                    ·
                      refine ⟨4180833430121497057854967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22297778293981317641893157 4180833430121497057854967)
                      ·
                        rfl

theorem cell23_8142144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_8142144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142144 prefixEnd_8142144 := by exact prefixLift 8142144
  have htrace : WordTrace (prefixWord ++ tailWord_8142144) baseStart_8142144 baseEnd_8142144 := by
    simpa [prefixWord, tailWord_8142144, baseEnd_8142144] using wordTrace_append hprefix tailTrace_8142144
  have hstable : (prefixWord ++ tailWord_8142144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142144).length < 2 ^ (prefixWord ++ tailWord_8142144).sum := by decide
  have hdescent : baseEnd_8142144 < baseStart_8142144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142173 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_8142173 : Nat := 118140960795 + 8142173 * 2 ^ 59
def prefixEnd_8142173 : Nat := 4983230072969 + 3 ^ 40 * 8142173 * 2
def baseEnd_8142173 : Nat := 4180848321060477444392335

theorem tailTrace_8142173 : CollatzResearch.WordTrace tailWord_8142173 prefixEnd_8142173 4180848321060477444392335 := by
  unfold tailWord_8142173
  simp only [CollatzResearch.WordTrace]
  refine ⟨296969446331305268284383173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197979630887536845522922115 296969446331305268284383173)
  ·
    refine ⟨55681771187119737803321845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296969446331305268284383173 55681771187119737803321845)
    ·
      refine ⟨5220166048792475419061423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55681771187119737803321845 5220166048792475419061423)
      ·
        refine ⟨7830249073188713128592135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220166048792475419061423 7830249073188713128592135)
        ·
          refine ⟨11745373609783069692888203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830249073188713128592135 11745373609783069692888203)
          ·
            refine ⟨17618060414674604539332305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11745373609783069692888203 17618060414674604539332305)
            ·
              refine ⟨13213545311005953404499229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17618060414674604539332305 13213545311005953404499229)
              ·
                refine ⟨4955079491627232526687211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13213545311005953404499229 4955079491627232526687211)
                ·
                  refine ⟨7432619237440848790030817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955079491627232526687211 7432619237440848790030817)
                  ·
                    refine ⟨5574464428080636592523113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7432619237440848790030817 5574464428080636592523113)
                    ·
                      refine ⟨4180848321060477444392335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574464428080636592523113 4180848321060477444392335)
                      ·
                        rfl

theorem cell23_8142173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_8142173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142173 prefixEnd_8142173 := by exact prefixLift 8142173
  have htrace : WordTrace (prefixWord ++ tailWord_8142173) baseStart_8142173 baseEnd_8142173 := by
    simpa [prefixWord, tailWord_8142173, baseEnd_8142173] using wordTrace_append hprefix tailTrace_8142173
  have hstable : (prefixWord ++ tailWord_8142173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142173).length < 2 ^ (prefixWord ++ tailWord_8142173).sum := by decide
  have hdescent : baseEnd_8142173 < baseStart_8142173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142206 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8142206 : Nat := 118140960795 + 8142206 * 2 ^ 59
def prefixEnd_8142206 : Nat := 4983230072969 + 3 ^ 40 * 8142206 * 2
def baseEnd_8142206 : Nat := 4180865265922075815279683

theorem tailTrace_8142206 : CollatzResearch.WordTrace tailWord_8142206 prefixEnd_8142206 4180865265922075815279683 := by
  unfold tailWord_8142206
  simp only [CollatzResearch.WordTrace]
  refine ⟨37121331242523214365041809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197980433293457143280222981 37121331242523214365041809)
  ·
    refine ⟨27840998431892410773781357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37121331242523214365041809 27840998431892410773781357)
    ·
      refine ⟨10440374411959654040168009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27840998431892410773781357 10440374411959654040168009)
      ·
        refine ⟨7830280808969740530126007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10440374411959654040168009 7830280808969740530126007)
        ·
          refine ⟨11745421213454610795189011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830280808969740530126007 11745421213454610795189011)
          ·
            refine ⟨17618131820181916192783517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11745421213454610795189011 17618131820181916192783517)
            ·
              refine ⟨6606799432568218572293819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17618131820181916192783517 6606799432568218572293819)
              ·
                refine ⟨9910199148852327858440729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606799432568218572293819 9910199148852327858440729)
                ·
                  refine ⟨7432649361639245893830547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9910199148852327858440729 7432649361639245893830547)
                  ·
                    refine ⟨11148974042458868840745821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7432649361639245893830547 11148974042458868840745821)
                    ·
                      refine ⟨4180865265922075815279683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11148974042458868840745821 4180865265922075815279683)
                      ·
                        rfl

theorem cell23_8142206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8142206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142206 prefixEnd_8142206 := by exact prefixLift 8142206
  have htrace : WordTrace (prefixWord ++ tailWord_8142206) baseStart_8142206 baseEnd_8142206 := by
    simpa [prefixWord, tailWord_8142206, baseEnd_8142206] using wordTrace_append hprefix tailTrace_8142206
  have hstable : (prefixWord ++ tailWord_8142206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142206).length < 2 ^ (prefixWord ++ tailWord_8142206).sum := by decide
  have hdescent : baseEnd_8142206 < baseStart_8142206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142231 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 2, 5]
def baseStart_8142231 : Nat := 118140960795 + 8142231 * 2 ^ 59
def prefixEnd_8142231 : Nat := 4983230072969 + 3 ^ 40 * 8142231 * 2
def baseEnd_8142231 : Nat := 1393626034312812739155689

theorem tailTrace_8142231 : CollatzResearch.WordTrace tailWord_8142231 prefixEnd_8142231 1393626034312812739155689 := by
  unfold tailWord_8142231
  simp only [CollatzResearch.WordTrace]
  refine ⟨296971561765095144189994547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197981041176730096126663031 296971561765095144189994547)
  ·
    refine ⟨445457342647642716284991821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296971561765095144189994547 445457342647642716284991821)
    ·
      refine ⟨167046503492866018606871933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445457342647642716284991821 167046503492866018606871933)
      ·
        refine ⟨62642438809824756977576975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167046503492866018606871933 62642438809824756977576975)
        ·
          refine ⟨93963658214737135466365463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62642438809824756977576975 93963658214737135466365463)
          ·
            refine ⟨140945487322105703199548195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93963658214737135466365463 140945487322105703199548195)
            ·
              refine ⟨211418230983158554799322293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140945487322105703199548195 211418230983158554799322293)
              ·
                refine ⟨19820459154671114512436465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211418230983158554799322293 19820459154671114512436465)
                ·
                  refine ⟨14865344366003335884327349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19820459154671114512436465 14865344366003335884327349)
                  ·
                    refine ⟨1393626034312812739155689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14865344366003335884327349 1393626034312812739155689)
                    ·
                      rfl

theorem cell23_8142231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_8142231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142231 prefixEnd_8142231 := by exact prefixLift 8142231
  have htrace : WordTrace (prefixWord ++ tailWord_8142231) baseStart_8142231 baseEnd_8142231 := by
    simpa [prefixWord, tailWord_8142231, baseEnd_8142231] using wordTrace_append hprefix tailTrace_8142231
  have hstable : (prefixWord ++ tailWord_8142231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142231).length < 2 ^ (prefixWord ++ tailWord_8142231).sum := by decide
  have hdescent : baseEnd_8142231 < baseStart_8142231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142271 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_8142271 : Nat := 118140960795 + 8142271 * 2 ^ 59
def prefixEnd_8142271 : Nat := 4983230072969 + 3 ^ 40 * 8142271 * 2
def baseEnd_8142271 : Nat := 4180898642164618060966883

theorem tailTrace_8142271 : CollatzResearch.WordTrace tailWord_8142271 prefixEnd_8142271 4180898642164618060966883 := by
  unfold tailWord_8142271
  simp only [CollatzResearch.WordTrace]
  refine ⟨296973020684950231021450667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197982013789966820680967111 296973020684950231021450667)
  ·
    refine ⟨445459531027425346532176001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296973020684950231021450667 445459531027425346532176001)
    ·
      refine ⟨334094648270569009899132001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445459531027425346532176001 334094648270569009899132001)
      ·
        refine ⟨250570986202926757424349001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334094648270569009899132001 250570986202926757424349001)
        ·
          refine ⟨187928239652195068068261751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250570986202926757424349001 187928239652195068068261751)
          ·
            refine ⟨281892359478292602102392627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187928239652195068068261751 281892359478292602102392627)
            ·
              refine ⟨422838539217438903153588941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281892359478292602102392627 422838539217438903153588941)
              ·
                refine ⟨158564452206539588682595853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422838539217438903153588941 158564452206539588682595853)
                ·
                  refine ⟨59461669577452345755973445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158564452206539588682595853 59461669577452345755973445)
                  ·
                    refine ⟨11149063045772314829245021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59461669577452345755973445 11149063045772314829245021)
                    ·
                      refine ⟨4180898642164618060966883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11149063045772314829245021 4180898642164618060966883)
                      ·
                        rfl

theorem cell23_8142271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_8142271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142271 prefixEnd_8142271 := by exact prefixLift 8142271
  have htrace : WordTrace (prefixWord ++ tailWord_8142271) baseStart_8142271 baseEnd_8142271 := by
    simpa [prefixWord, tailWord_8142271, baseEnd_8142271] using wordTrace_append hprefix tailTrace_8142271
  have hstable : (prefixWord ++ tailWord_8142271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142271).length < 2 ^ (prefixWord ++ tailWord_8142271).sum := by decide
  have hdescent : baseEnd_8142271 < baseStart_8142271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142325 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 6]
def baseStart_8142325 : Nat := 118140960795 + 8142325 * 2 ^ 59
def prefixEnd_8142325 : Nat := 4983230072969 + 3 ^ 40 * 8142325 * 2
def baseEnd_8142325 : Nat := 464547374457773427743515

theorem tailTrace_8142325 : CollatzResearch.WordTrace tailWord_8142325 prefixEnd_8142325 464547374457773427743515 := by
  unfold tailWord_8142325
  simp only [CollatzResearch.WordTrace]
  refine ⟨296974990226754598243916429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197983326817836398829277619 296974990226754598243916429)
  ·
    refine ⟨111365621335032974341468661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296974990226754598243916429 111365621335032974341468661)
    ·
      refine ⟨10440527000159341344512687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111365621335032974341468661 10440527000159341344512687)
      ·
        refine ⟨15660790500239012016769031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10440527000159341344512687 15660790500239012016769031)
        ·
          refine ⟨23491185750358518025153547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660790500239012016769031 23491185750358518025153547)
          ·
            refine ⟨35236778625537777037730321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23491185750358518025153547 35236778625537777037730321)
            ·
              refine ⟨26427583969153332778297741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35236778625537777037730321 26427583969153332778297741)
              ·
                refine ⟨9910343988432499791861653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26427583969153332778297741 9910343988432499791861653)
                ·
                  refine ⟨464547374457773427743515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9910343988432499791861653 464547374457773427743515)
                  ·
                    rfl

theorem cell23_8142325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_8142325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142325 prefixEnd_8142325 := by exact prefixLift 8142325
  have htrace : WordTrace (prefixWord ++ tailWord_8142325) baseStart_8142325 baseEnd_8142325 := by
    simpa [prefixWord, tailWord_8142325, baseEnd_8142325] using wordTrace_append hprefix tailTrace_8142325
  have hstable : (prefixWord ++ tailWord_8142325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142325).length < 2 ^ (prefixWord ++ tailWord_8142325).sum := by decide
  have hdescent : baseEnd_8142325 < baseStart_8142325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142355 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 1, 5]
def baseStart_8142355 : Nat := 118140960795 + 8142355 * 2 ^ 59
def prefixEnd_8142355 : Nat := 4983230072969 + 3 ^ 40 * 8142355 * 2
def baseEnd_8142355 : Nat := 1393647258179865244105499

theorem tailTrace_8142355 : CollatzResearch.WordTrace tailWord_8142355 prefixEnd_8142355 1393647258179865244105499 := by
  unfold tailWord_8142355
  simp only [CollatzResearch.WordTrace]
  refine ⟨296976084416645913367508519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197984056277763942245005679 296976084416645913367508519)
  ·
    refine ⟨445464126624968870051262779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296976084416645913367508519 445464126624968870051262779)
    ·
      refine ⟨668196189937453305076894169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445464126624968870051262779 668196189937453305076894169)
      ·
        refine ⟨501147142453089978807670627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668196189937453305076894169 501147142453089978807670627)
        ·
          refine ⟨751720713679634968211505941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501147142453089978807670627 751720713679634968211505941)
          ·
            refine ⟨35236908453732889134914341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 751720713679634968211505941 35236908453732889134914341)
            ·
              refine ⟨6606920335074916712796439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35236908453732889134914341 6606920335074916712796439)
              ·
                refine ⟨9910380502612375069194659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606920335074916712796439 9910380502612375069194659)
                ·
                  refine ⟨14865570753918562603791989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910380502612375069194659 14865570753918562603791989)
                  ·
                    refine ⟨1393647258179865244105499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14865570753918562603791989 1393647258179865244105499)
                    ·
                      rfl

theorem cell23_8142355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 5].length) (baseStart_8142355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142355 prefixEnd_8142355 := by exact prefixLift 8142355
  have htrace : WordTrace (prefixWord ++ tailWord_8142355) baseStart_8142355 baseEnd_8142355 := by
    simpa [prefixWord, tailWord_8142355, baseEnd_8142355] using wordTrace_append hprefix tailTrace_8142355
  have hstable : (prefixWord ++ tailWord_8142355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142355).length < 2 ^ (prefixWord ++ tailWord_8142355).sum := by decide
  have hdescent : baseEnd_8142355 < baseStart_8142355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142392 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 3, 2, 2]
def baseStart_8142392 : Nat := 118140960795 + 8142392 * 2 ^ 59
def prefixEnd_8142392 : Nat := 4983230072969 + 3 ^ 40 * 8142392 * 2
def baseEnd_8142392 : Nat := 4180960773323812087553827

theorem tailTrace_8142392 : CollatzResearch.WordTrace tailWord_8142392 prefixEnd_8142392 4180960773323812087553827 := by
  unfold tailWord_8142392
  simp only [CollatzResearch.WordTrace]
  refine ⟨148488716958755934343302715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197984955945007912457736953 148488716958755934343302715)
  ·
    refine ⟨222733075438133901514954073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148488716958755934343302715 222733075438133901514954073)
    ·
      refine ⟨167049806578600426136215555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222733075438133901514954073 167049806578600426136215555)
      ·
        refine ⟨250574709867900639204323333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167049806578600426136215555 250574709867900639204323333)
        ·
          refine ⟨46982758100231369850810625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250574709867900639204323333 46982758100231369850810625)
          ·
            refine ⟨35237068575173527388107969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46982758100231369850810625 35237068575173527388107969)
            ·
              refine ⟨26427801431380145541080977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35237068575173527388107969 26427801431380145541080977)
              ·
                refine ⟨19820851073535109155810733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26427801431380145541080977 19820851073535109155810733)
                ·
                  refine ⟨7432819152575665933429025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19820851073535109155810733 7432819152575665933429025)
                  ·
                    refine ⟨5574614364431749450071769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7432819152575665933429025 5574614364431749450071769)
                    ·
                      refine ⟨4180960773323812087553827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574614364431749450071769 4180960773323812087553827)
                      ·
                        rfl

theorem cell23_8142392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_8142392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142392 prefixEnd_8142392 := by exact prefixLift 8142392
  have htrace : WordTrace (prefixWord ++ tailWord_8142392) baseStart_8142392 baseEnd_8142392 := by
    simpa [prefixWord, tailWord_8142392, baseEnd_8142392] using wordTrace_append hprefix tailTrace_8142392
  have hstable : (prefixWord ++ tailWord_8142392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142392).length < 2 ^ (prefixWord ++ tailWord_8142392).sum := by decide
  have hdescent : baseEnd_8142392 < baseStart_8142392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142411 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 9]
def baseStart_8142411 : Nat := 118140960795 + 8142411 * 2 ^ 59
def prefixEnd_8142411 : Nat := 4983230072969 + 3 ^ 40 * 8142411 * 2
def baseEnd_8142411 : Nat := 1393656843152082504405413

theorem tailTrace_8142411 : CollatzResearch.WordTrace tailWord_8142411 prefixEnd_8142411 1393656843152082504405413 := by
  unfold tailWord_8142411
  simp only [CollatzResearch.WordTrace]
  refine ⟨296978126904443034931547087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197985417936295356621031391 296978126904443034931547087)
  ·
    refine ⟨445467190356664552397320631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296978126904443034931547087 445467190356664552397320631)
    ·
      refine ⟨668200785534996828595980947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445467190356664552397320631 668200785534996828595980947)
      ·
        refine ⟨1002301178302495242893971421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668200785534996828595980947 1002301178302495242893971421)
        ·
          refine ⟨375862941863435716085239283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002301178302495242893971421 375862941863435716085239283)
          ·
            refine ⟨563794412795153574127858925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375862941863435716085239283 563794412795153574127858925)
            ·
              refine ⟨211422904798182590297947097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563794412795153574127858925 211422904798182590297947097)
              ·
                refine ⟨158567178598636942723460323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211422904798182590297947097 158567178598636942723460323)
                ·
                  refine ⟨237850767897955414085190485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158567178598636942723460323 237850767897955414085190485)
                  ·
                    refine ⟨1393656843152082504405413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 237850767897955414085190485 1393656843152082504405413)
                    ·
                      rfl

theorem cell23_8142411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_8142411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142411 prefixEnd_8142411 := by exact prefixLift 8142411
  have htrace : WordTrace (prefixWord ++ tailWord_8142411) baseStart_8142411 baseEnd_8142411 := by
    simpa [prefixWord, tailWord_8142411, baseEnd_8142411] using wordTrace_append hprefix tailTrace_8142411
  have hstable : (prefixWord ++ tailWord_8142411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142411).length < 2 ^ (prefixWord ++ tailWord_8142411).sum := by decide
  have hdescent : baseEnd_8142411 < baseStart_8142411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142446 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_8142446 : Nat := 118140960795 + 8142446 * 2 ^ 59
def prefixEnd_8142446 : Nat := 4983230072969 + 3 ^ 40 * 8142446 * 2
def baseEnd_8142446 : Nat := 4180988501279154876278579

theorem tailTrace_8142446 : CollatzResearch.WordTrace tailWord_8142446 prefixEnd_8142446 4180988501279154876278579 := by
  unfold tailWord_8142446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37122425432414529488633899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197986268972877490606047461 37122425432414529488633899)
  ·
    refine ⟨55683638148621794232950849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37122425432414529488633899 55683638148621794232950849)
    ·
      refine ⟨41762728611466345674713137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55683638148621794232950849 41762728611466345674713137)
      ·
        refine ⟨31322046458599759256034853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41762728611466345674713137 31322046458599759256034853)
        ·
          refine ⟨5872883710987454860506535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31322046458599759256034853 5872883710987454860506535)
          ·
            refine ⟨8809325566481182290759803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872883710987454860506535 8809325566481182290759803)
            ·
              refine ⟨13213988349721773436139705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809325566481182290759803 13213988349721773436139705)
              ·
                refine ⟨9910491262291330077104779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13213988349721773436139705 9910491262291330077104779)
                ·
                  refine ⟨14865736893436995115657169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910491262291330077104779 14865736893436995115657169)
                  ·
                    refine ⟨11149302670077746336742877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14865736893436995115657169 11149302670077746336742877)
                    ·
                      refine ⟨4180988501279154876278579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11149302670077746336742877 4180988501279154876278579)
                      ·
                        rfl

theorem cell23_8142446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_8142446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142446 prefixEnd_8142446 := by exact prefixLift 8142446
  have htrace : WordTrace (prefixWord ++ tailWord_8142446) baseStart_8142446 baseEnd_8142446 := by
    simpa [prefixWord, tailWord_8142446, baseEnd_8142446] using wordTrace_append hprefix tailTrace_8142446
  have hstable : (prefixWord ++ tailWord_8142446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142446).length < 2 ^ (prefixWord ++ tailWord_8142446).sum := by decide
  have hdescent : baseEnd_8142446 < baseStart_8142446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142469 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 1, 3, 2]
def baseStart_8142469 : Nat := 118140960795 + 8142469 * 2 ^ 59
def prefixEnd_8142469 : Nat := 4983230072969 + 3 ^ 40 * 8142469 * 2
def baseEnd_8142469 : Nat := 4181000311334208286290973

theorem tailTrace_8142469 : CollatzResearch.WordTrace tailWord_8142469 prefixEnd_8142469 4181000311334208286290973 := by
  unfold tailWord_8142469
  simp only [CollatzResearch.WordTrace]
  refine ⟨296980242338232910837158461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197986828225488607224772307 296980242338232910837158461)
  ·
    refine ⟨111367590876837341563934423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296980242338232910837158461 111367590876837341563934423)
    ·
      refine ⟨167051386315256012345901635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111367590876837341563934423 167051386315256012345901635)
      ·
        refine ⟨250577079472884018518852453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167051386315256012345901635 250577079472884018518852453)
        ·
          refine ⟨46983202401165753472284835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250577079472884018518852453 46983202401165753472284835)
          ·
            refine ⟨70474803601748630208427253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46983202401165753472284835 70474803601748630208427253)
            ·
              refine ⟨6607012837663934082040055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70474803601748630208427253 6607012837663934082040055)
              ·
                refine ⟨9910519256495901123060083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607012837663934082040055 9910519256495901123060083)
                ·
                  refine ⟨14865778884743851684590125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910519256495901123060083 14865778884743851684590125)
                  ·
                    refine ⟨5574667081778944381721297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14865778884743851684590125 5574667081778944381721297)
                    ·
                      refine ⟨4181000311334208286290973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574667081778944381721297 4181000311334208286290973)
                      ·
                        rfl

theorem cell23_8142469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_8142469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142469 prefixEnd_8142469 := by exact prefixLift 8142469
  have htrace : WordTrace (prefixWord ++ tailWord_8142469) baseStart_8142469 baseEnd_8142469 := by
    simpa [prefixWord, tailWord_8142469, baseEnd_8142469] using wordTrace_append hprefix tailTrace_8142469
  have hstable : (prefixWord ++ tailWord_8142469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142469).length < 2 ^ (prefixWord ++ tailWord_8142469).sum := by decide
  have hdescent : baseEnd_8142469 < baseStart_8142469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142522 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_8142522 : Nat := 118140960795 + 8142522 * 2 ^ 59
def prefixEnd_8142522 : Nat := 4983230072969 + 3 ^ 40 * 8142522 * 2
def baseEnd_8142522 : Nat := 464558613978766286547581

theorem tailTrace_8142522 : CollatzResearch.WordTrace tailWord_8142522 prefixEnd_8142522 464558613978766286547581 := by
  unfold tailWord_8142522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74245543851760225222209455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197988116938027267259225213 74245543851760225222209455)
  ·
    refine ⟨111368315777640337833314183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74245543851760225222209455 111368315777640337833314183)
    ·
      refine ⟨167052473666460506749971275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111368315777640337833314183 167052473666460506749971275)
      ·
        refine ⟨250578710499690760124956913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167052473666460506749971275 250578710499690760124956913)
        ·
          refine ⟨187934032874768070093717685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250578710499690760124956913 187934032874768070093717685)
          ·
            refine ⟨17618815582009506571286033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187934032874768070093717685 17618815582009506571286033)
            ·
              refine ⟨13214111686507129928464525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17618815582009506571286033 13214111686507129928464525)
              ·
                refine ⟨4955291882440173723174197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13214111686507129928464525 4955291882440173723174197)
                ·
                  refine ⟨464558613978766286547581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4955291882440173723174197 464558613978766286547581)
                  ·
                    rfl

theorem cell23_8142522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_8142522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142522 prefixEnd_8142522 := by exact prefixLift 8142522
  have htrace : WordTrace (prefixWord ++ tailWord_8142522) baseStart_8142522 baseEnd_8142522 := by
    simpa [prefixWord, tailWord_8142522, baseEnd_8142522] using wordTrace_append hprefix tailTrace_8142522
  have hstable : (prefixWord ++ tailWord_8142522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142522).length < 2 ^ (prefixWord ++ tailWord_8142522).sum := by decide
  have hdescent : baseEnd_8142522 < baseStart_8142522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142550 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_8142550 : Nat := 118140960795 + 8142550 * 2 ^ 59
def prefixEnd_8142550 : Nat := 4983230072969 + 3 ^ 40 * 8142550 * 2
def baseEnd_8142550 : Nat := 4181041903267222469378101

theorem tailTrace_8142550 : CollatzResearch.WordTrace tailWord_8142550 prefixEnd_8142550 4181041903267222469378101 := by
  unfold tailWord_8142550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18561449790683716354428569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197988797767292974447238069 18561449790683716354428569)
  ·
    refine ⟨13921087343012787265821427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18561449790683716354428569 13921087343012787265821427)
    ·
      refine ⟨20881631014519180898732141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921087343012787265821427 20881631014519180898732141)
      ·
        refine ⟨7830611630444692837024553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20881631014519180898732141 7830611630444692837024553)
        ·
          refine ⟨5872958722833519627768415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830611630444692837024553 5872958722833519627768415)
          ·
            refine ⟨8809438084250279441652623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872958722833519627768415 8809438084250279441652623)
            ·
              refine ⟨13214157126375419162478935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809438084250279441652623 13214157126375419162478935)
              ·
                refine ⟨19821235689563128743718403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13214157126375419162478935 19821235689563128743718403)
                ·
                  refine ⟨29731853534344693115577605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19821235689563128743718403 29731853534344693115577605)
                  ·
                    refine ⟨5574722537689629959170801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29731853534344693115577605 5574722537689629959170801)
                    ·
                      refine ⟨4181041903267222469378101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574722537689629959170801 4181041903267222469378101)
                      ·
                        rfl

theorem cell23_8142550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_8142550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142550 prefixEnd_8142550 := by exact prefixLift 8142550
  have htrace : WordTrace (prefixWord ++ tailWord_8142550) baseStart_8142550 baseEnd_8142550 := by
    simpa [prefixWord, tailWord_8142550, baseEnd_8142550] using wordTrace_append hprefix tailTrace_8142550
  have hstable : (prefixWord ++ tailWord_8142550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142550).length < 2 ^ (prefixWord ++ tailWord_8142550).sum := by decide
  have hdescent : baseEnd_8142550 < baseStart_8142550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142575 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_8142575 : Nat := 118140960795 + 8142575 * 2 ^ 59
def prefixEnd_8142575 : Nat := 4983230072969 + 3 ^ 40 * 8142575 * 2
def baseEnd_8142575 : Nat := 4181054740283584871565485

theorem tailTrace_8142575 : CollatzResearch.WordTrace tailWord_8142575 prefixEnd_8142575 4181054740283584871565485 := by
  unfold tailWord_8142575
  simp only [CollatzResearch.WordTrace]
  refine ⟨296984108475848890940517179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197989405650565927293678119 296984108475848890940517179)
  ·
    refine ⟨445476162713773336410775769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296984108475848890940517179 445476162713773336410775769)
    ·
      refine ⟨334107122035330002308081827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445476162713773336410775769 334107122035330002308081827)
      ·
        refine ⟨501160683052995003462122741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334107122035330002308081827 501160683052995003462122741)
        ·
          refine ⟨46983814036218281574574007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 501160683052995003462122741 46983814036218281574574007)
          ·
            refine ⟨70475721054327422361861011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46983814036218281574574007 70475721054327422361861011)
            ·
              refine ⟨105713581581491133542791517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70475721054327422361861011 105713581581491133542791517)
              ·
                refine ⟨39642593093059175078546819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105713581581491133542791517 39642593093059175078546819)
                ·
                  refine ⟨59463889639588762617820229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39642593093059175078546819 59463889639588762617820229)
                  ·
                    refine ⟨11149479307422892990841293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59463889639588762617820229 11149479307422892990841293)
                    ·
                      refine ⟨4181054740283584871565485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11149479307422892990841293 4181054740283584871565485)
                      ·
                        rfl

theorem cell23_8142575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_8142575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142575 prefixEnd_8142575 := by exact prefixLift 8142575
  have htrace : WordTrace (prefixWord ++ tailWord_8142575) baseStart_8142575 baseEnd_8142575 := by
    simpa [prefixWord, tailWord_8142575, baseEnd_8142575] using wordTrace_append hprefix tailTrace_8142575
  have hstable : (prefixWord ++ tailWord_8142575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142575).length < 2 ^ (prefixWord ++ tailWord_8142575).sum := by decide
  have hdescent : baseEnd_8142575 < baseStart_8142575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142665 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_8142665 : Nat := 118140960795 + 8142665 * 2 ^ 59
def prefixEnd_8142665 : Nat := 4983230072969 + 3 ^ 40 * 8142665 * 2
def baseEnd_8142665 : Nat := 4181100953542489519440071

theorem tailTrace_8142665 : CollatzResearch.WordTrace tailWord_8142665 prefixEnd_8142665 4181100953542489519440071 := by
  unfold tailWord_8142665
  simp only [CollatzResearch.WordTrace]
  refine ⟨296987391045522836311293449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197991594030348557540862299 296987391045522836311293449)
  ·
    refine ⟨222740543284142127233470087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296987391045522836311293449 222740543284142127233470087)
    ·
      refine ⟨334110814926213190850205131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222740543284142127233470087 334110814926213190850205131)
      ·
        refine ⟨501166222389319786275307697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334110814926213190850205131 501166222389319786275307697)
        ·
          refine ⟨375874666791989839706480773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501166222389319786275307697 375874666791989839706480773)
          ·
            refine ⟨70476500023498094944965145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375874666791989839706480773 70476500023498094944965145)
            ·
              refine ⟨52857375017623571208723859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70476500023498094944965145 52857375017623571208723859)
              ·
                refine ⟨79286062526435356813085789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52857375017623571208723859 79286062526435356813085789)
                ·
                  refine ⟨29732273447413258804907171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79286062526435356813085789 29732273447413258804907171)
                  ·
                    refine ⟨44598410171119888207360757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29732273447413258804907171 44598410171119888207360757)
                    ·
                      refine ⟨4181100953542489519440071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44598410171119888207360757 4181100953542489519440071)
                      ·
                        rfl

theorem cell23_8142665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_8142665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142665 prefixEnd_8142665 := by exact prefixLift 8142665
  have htrace : WordTrace (prefixWord ++ tailWord_8142665) baseStart_8142665 baseEnd_8142665 := by
    simpa [prefixWord, tailWord_8142665, baseEnd_8142665] using wordTrace_append hprefix tailTrace_8142665
  have hstable : (prefixWord ++ tailWord_8142665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142665).length < 2 ^ (prefixWord ++ tailWord_8142665).sum := by decide
  have hdescent : baseEnd_8142665 < baseStart_8142665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142682 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_8142682 : Nat := 118140960795 + 8142682 * 2 ^ 59
def prefixEnd_8142682 : Nat := 4983230072969 + 3 ^ 40 * 8142682 * 2
def baseEnd_8142682 : Nat := 4181109682713615952927493

theorem tailTrace_8142682 : CollatzResearch.WordTrace tailWord_8142682 prefixEnd_8142682 4181109682713615952927493 := by
  unfold tailWord_8142682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74247002771615312053665575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197992007390974165476441533 74247002771615312053665575)
  ·
    refine ⟨111370504157422968080498363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74247002771615312053665575 111370504157422968080498363)
    ·
      refine ⟨167055756236134452120747545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111370504157422968080498363 167055756236134452120747545)
      ·
        refine ⟨125291817177100839090560659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167055756236134452120747545 125291817177100839090560659)
        ·
          refine ⟨187937725765651258635840989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125291817177100839090560659 187937725765651258635840989)
          ·
            refine ⟨70476647162119221988440371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187937725765651258635840989 70476647162119221988440371)
            ·
              refine ⟨105714970743178832982660557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70476647162119221988440371 105714970743178832982660557)
              ·
                refine ⟨39643114028692062368497709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105714970743178832982660557 39643114028692062368497709)
                ·
                  refine ⟨14866167760759523388186641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39643114028692062368497709 14866167760759523388186641)
                  ·
                    refine ⟨11149625820569642541139981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14866167760759523388186641 11149625820569642541139981)
                    ·
                      refine ⟨4181109682713615952927493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11149625820569642541139981 4181109682713615952927493)
                      ·
                        rfl

theorem cell23_8142682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_8142682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142682 prefixEnd_8142682 := by exact prefixLift 8142682
  have htrace : WordTrace (prefixWord ++ tailWord_8142682) baseStart_8142682 baseEnd_8142682 := by
    simpa [prefixWord, tailWord_8142682, baseEnd_8142682] using wordTrace_append hprefix tailTrace_8142682
  have hstable : (prefixWord ++ tailWord_8142682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142682).length < 2 ^ (prefixWord ++ tailWord_8142682).sum := by decide
  have hdescent : baseEnd_8142682 < baseStart_8142682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142702 : List Nat := [4, 1, 2, 3, 1, 2, 10]
def baseStart_8142702 : Nat := 118140960795 + 8142702 * 2 ^ 59
def prefixEnd_8142702 : Nat := 4983230072969 + 3 ^ 40 * 8142702 * 2
def baseEnd_8142702 : Nat := 51618764843539578699721

theorem tailTrace_8142702 : CollatzResearch.WordTrace tailWord_8142702 prefixEnd_8142702 51618764843539578699721 := by
  unfold tailWord_8142702
  simp only [CollatzResearch.WordTrace]
  refine ⟨37123592568298598953798795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197992493697592527753593573 37123592568298598953798795)
  ·
    refine ⟨55685388852447898430698193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37123592568298598953798795 55685388852447898430698193)
    ·
      refine ⟨41764041639335923823023645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55685388852447898430698193 41764041639335923823023645)
      ·
        refine ⟨15661515614750971433633867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41764041639335923823023645 15661515614750971433633867)
        ·
          refine ⟨23492273422126457150450801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15661515614750971433633867 23492273422126457150450801)
          ·
            refine ⟨17619205066594842862838101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23492273422126457150450801 17619205066594842862838101)
            ·
              refine ⟨51618764843539578699721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17619205066594842862838101 51618764843539578699721)
              ·
                rfl

theorem cell23_8142702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 10].length) (baseStart_8142702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142702 prefixEnd_8142702 := by exact prefixLift 8142702
  have htrace : WordTrace (prefixWord ++ tailWord_8142702) baseStart_8142702 baseEnd_8142702 := by
    simpa [prefixWord, tailWord_8142702, baseEnd_8142702] using wordTrace_append hprefix tailTrace_8142702
  have hstable : (prefixWord ++ tailWord_8142702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142702).length < 2 ^ (prefixWord ++ tailWord_8142702).sum := by decide
  have hdescent : baseEnd_8142702 < baseStart_8142702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142735 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_8142735 : Nat := 118140960795 + 8142735 * 2 ^ 59
def prefixEnd_8142735 : Nat := 4983230072969 + 3 ^ 40 * 8142735 * 2
def baseEnd_8142735 : Nat := 4181136897188304245564749

theorem tailTrace_8142735 : CollatzResearch.WordTrace tailWord_8142735 prefixEnd_8142735 4181136897188304245564749 := by
  unfold tailWord_8142735
  simp only [CollatzResearch.WordTrace]
  refine ⟨296989944155269238266341659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197993296103512825510894439 296989944155269238266341659)
  ·
    refine ⟨445484916232903857399512489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296989944155269238266341659 445484916232903857399512489)
    ·
      refine ⟨334113687174677893049634367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445484916232903857399512489 334113687174677893049634367)
      ·
        refine ⟨501170530762016839574451551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334113687174677893049634367 501170530762016839574451551)
        ·
          refine ⟨751755796143025259361677327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501170530762016839574451551 751755796143025259361677327)
          ·
            refine ⟨1127633694214537889042515991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751755796143025259361677327 1127633694214537889042515991)
            ·
              refine ⟨1691450541321806833563773987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127633694214537889042515991 1691450541321806833563773987)
              ·
                refine ⟨2537175811982710250345660981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691450541321806833563773987 2537175811982710250345660981)
                ·
                  refine ⟨237860232373379085969905717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2537175811982710250345660981 237860232373379085969905717)
                  ·
                    refine ⟨22299396785004289309678661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237860232373379085969905717 22299396785004289309678661)
                    ·
                      refine ⟨4181136897188304245564749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22299396785004289309678661 4181136897188304245564749)
                      ·
                        rfl

theorem cell23_8142735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_8142735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142735 prefixEnd_8142735 := by exact prefixLift 8142735
  have htrace : WordTrace (prefixWord ++ tailWord_8142735) baseStart_8142735 baseEnd_8142735 := by
    simpa [prefixWord, tailWord_8142735, baseEnd_8142735] using wordTrace_append hprefix tailTrace_8142735
  have hstable : (prefixWord ++ tailWord_8142735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142735).length < 2 ^ (prefixWord ++ tailWord_8142735).sum := by decide
  have hdescent : baseEnd_8142735 < baseStart_8142735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142745 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_8142745 : Nat := 118140960795 + 8142745 * 2 ^ 59
def prefixEnd_8142745 : Nat := 4983230072969 + 3 ^ 40 * 8142745 * 2
def baseEnd_8142745 : Nat := 1393714010664949735479901

theorem tailTrace_8142745 : CollatzResearch.WordTrace tailWord_8142745 prefixEnd_8142745 1393714010664949735479901 := by
  unfold tailWord_8142745
  simp only [CollatzResearch.WordTrace]
  refine ⟨296990308885233009974205689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197993539256822006649470459 296990308885233009974205689)
  ·
    refine ⟨222742731663924757480654267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296990308885233009974205689 222742731663924757480654267)
    ·
      refine ⟨334114097495887136220981401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222742731663924757480654267 334114097495887136220981401)
      ·
        refine ⟨250585573121915352165736051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334114097495887136220981401 250585573121915352165736051)
        ·
          refine ⟨375878359682873028248604077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250585573121915352165736051 375878359682873028248604077)
          ·
            refine ⟨140954384881077385593226529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375878359682873028248604077 140954384881077385593226529)
            ·
              refine ⟨105715788660808039194919897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140954384881077385593226529 105715788660808039194919897)
              ·
                refine ⟨79286841495606029396189923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105715788660808039194919897 79286841495606029396189923)
                ·
                  refine ⟨118930262243409044094284885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79286841495606029396189923 118930262243409044094284885)
                  ·
                    refine ⟨1393714010664949735479901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118930262243409044094284885 1393714010664949735479901)
                    ·
                      rfl

theorem cell23_8142745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_8142745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142745 prefixEnd_8142745 := by exact prefixLift 8142745
  have htrace : WordTrace (prefixWord ++ tailWord_8142745) baseStart_8142745 baseEnd_8142745 := by
    simpa [prefixWord, tailWord_8142745, baseEnd_8142745] using wordTrace_append hprefix tailTrace_8142745
  have hstable : (prefixWord ++ tailWord_8142745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142745).length < 2 ^ (prefixWord ++ tailWord_8142745).sum := by decide
  have hdescent : baseEnd_8142745 < baseStart_8142745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142756 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_8142756 : Nat := 118140960795 + 8142756 * 2 ^ 59
def prefixEnd_8142756 : Nat := 4983230072969 + 3 ^ 40 * 8142756 * 2
def baseEnd_8142756 : Nat := 4181147680282048663402153

theorem tailTrace_8142756 : CollatzResearch.WordTrace tailWord_8142756 prefixEnd_8142756 4181147680282048663402153 := by
  unfold tailWord_8142756
  simp only [CollatzResearch.WordTrace]
  refine ⟨148495355044096579426428061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197993806725462105901904081 148495355044096579426428061)
  ·
    refine ⟨55685758141536217284910523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148495355044096579426428061 55685758141536217284910523)
    ·
      refine ⟨83528637212304325927365785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55685758141536217284910523 83528637212304325927365785)
      ·
        refine ⟨62646477909228244445524339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83528637212304325927365785 62646477909228244445524339)
        ·
          refine ⟨93969716863842366668286509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62646477909228244445524339 93969716863842366668286509)
          ·
            refine ⟨35238643823940887500607441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93969716863842366668286509 35238643823940887500607441)
            ·
              refine ⟨26428982867955665625455581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35238643823940887500607441 26428982867955665625455581)
              ·
                refine ⟨9910868575483374609545843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26428982867955665625455581 9910868575483374609545843)
                ·
                  refine ⟨14866302863225061914318765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910868575483374609545843 14866302863225061914318765)
                  ·
                    refine ⟨5574863573709398217869537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14866302863225061914318765 5574863573709398217869537)
                    ·
                      refine ⟨4181147680282048663402153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574863573709398217869537 4181147680282048663402153)
                      ·
                        rfl

theorem cell23_8142756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_8142756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142756 prefixEnd_8142756 := by exact prefixLift 8142756
  have htrace : WordTrace (prefixWord ++ tailWord_8142756) baseStart_8142756 baseEnd_8142756 := by
    simpa [prefixWord, tailWord_8142756, baseEnd_8142756] using wordTrace_append hprefix tailTrace_8142756
  have hstable : (prefixWord ++ tailWord_8142756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142756).length < 2 ^ (prefixWord ++ tailWord_8142756).sum := by decide
  have hdescent : baseEnd_8142756 < baseStart_8142756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142832 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_8142832 : Nat := 118140960795 + 8142832 * 2 ^ 59
def prefixEnd_8142832 : Nat := 4983230072969 + 3 ^ 40 * 8142832 * 2
def baseEnd_8142832 : Nat := 4181186704811790366051803

theorem tailTrace_8142832 : CollatzResearch.WordTrace tailWord_8142832 prefixEnd_8142832 4181186704811790366051803 := by
  unfold tailWord_8142832
  simp only [CollatzResearch.WordTrace]
  refine ⟨148496741017958911916311375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197995654690611882555081833 148496741017958911916311375)
  ·
    refine ⟨222745111526938367874467063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148496741017958911916311375 222745111526938367874467063)
    ·
      refine ⟨334117667290407551811700595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222745111526938367874467063 334117667290407551811700595)
      ·
        refine ⟨501176500935611327717550893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334117667290407551811700595 501176500935611327717550893)
        ·
          refine ⟨187941187850854247894081585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501176500935611327717550893 187941187850854247894081585)
          ·
            refine ⟨140955890888140685920561189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187941187850854247894081585 140955890888140685920561189)
            ·
              refine ⟨26429229541526378610105223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140955890888140685920561189 26429229541526378610105223)
              ·
                refine ⟨39643844312289567915157835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26429229541526378610105223 39643844312289567915157835)
                ·
                  refine ⟨59465766468434351872736753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39643844312289567915157835 59465766468434351872736753)
                  ·
                    refine ⟨44599324851325763904552565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59465766468434351872736753 44599324851325763904552565)
                    ·
                      refine ⟨4181186704811790366051803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44599324851325763904552565 4181186704811790366051803)
                      ·
                        rfl

theorem cell23_8142832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_8142832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142832 prefixEnd_8142832 := by exact prefixLift 8142832
  have htrace : WordTrace (prefixWord ++ tailWord_8142832) baseStart_8142832 baseEnd_8142832 := by
    simpa [prefixWord, tailWord_8142832, baseEnd_8142832] using wordTrace_append hprefix tailTrace_8142832
  have hstable : (prefixWord ++ tailWord_8142832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142832).length < 2 ^ (prefixWord ++ tailWord_8142832).sum := by decide
  have hdescent : baseEnd_8142832 < baseStart_8142832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142859 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 6, 2]
def baseStart_8142859 : Nat := 118140960795 + 8142859 * 2 ^ 59
def prefixEnd_8142859 : Nat := 4983230072969 + 3 ^ 40 * 8142859 * 2
def baseEnd_8142859 : Nat := 4181200568789461760414179

theorem tailTrace_8142859 : CollatzResearch.WordTrace tailWord_8142859 prefixEnd_8142859 4181200568789461760414179 := by
  unfold tailWord_8142859
  simp only [CollatzResearch.WordTrace]
  refine ⟨296994466806820007443855631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197996311204546671629237087 296994466806820007443855631)
  ·
    refine ⟨445491700210230011165783447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296994466806820007443855631 445491700210230011165783447)
    ·
      refine ⟨668237550315345016748675171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445491700210230011165783447 668237550315345016748675171)
      ·
        refine ⟨1002356325473017525123012757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668237550315345016748675171 1002356325473017525123012757)
        ·
          refine ⟨46985452756547696490141223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1002356325473017525123012757 46985452756547696490141223)
          ·
            refine ⟨70478179134821544735211835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46985452756547696490141223 70478179134821544735211835)
            ·
              refine ⟨105717268702232317102817753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70478179134821544735211835 105717268702232317102817753)
              ·
                refine ⟨79287951526674237827113315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105717268702232317102817753 79287951526674237827113315)
                ·
                  refine ⟨118931927290011356740669973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79287951526674237827113315 118931927290011356740669973)
                  ·
                    refine ⟨5574934091719282347218905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118931927290011356740669973 5574934091719282347218905)
                    ·
                      refine ⟨4181200568789461760414179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574934091719282347218905 4181200568789461760414179)
                      ·
                        rfl

theorem cell23_8142859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6, 2].length) (baseStart_8142859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142859 prefixEnd_8142859 := by exact prefixLift 8142859
  have htrace : WordTrace (prefixWord ++ tailWord_8142859) baseStart_8142859 baseEnd_8142859 := by
    simpa [prefixWord, tailWord_8142859, baseEnd_8142859] using wordTrace_append hprefix tailTrace_8142859
  have hstable : (prefixWord ++ tailWord_8142859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142859).length < 2 ^ (prefixWord ++ tailWord_8142859).sum := by decide
  have hdescent : baseEnd_8142859 < baseStart_8142859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142872 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_8142872 : Nat := 118140960795 + 8142872 * 2 ^ 59
def prefixEnd_8142872 : Nat := 4983230072969 + 3 ^ 40 * 8142872 * 2
def baseEnd_8142872 : Nat := 4181207244037970209551619

theorem tailTrace_8142872 : CollatzResearch.WordTrace tailWord_8142872 prefixEnd_8142872 4181207244037970209551619 := by
  unfold tailWord_8142872
  simp only [CollatzResearch.WordTrace]
  refine ⟨148497470477886455332039435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197996627303848607109385913 148497470477886455332039435)
  ·
    refine ⟨222746205716829682998059153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148497470477886455332039435 222746205716829682998059153)
    ·
      refine ⟨167059654287622262248544365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222746205716829682998059153 167059654287622262248544365)
      ·
        refine ⟨62647370357858348343204137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167059654287622262248544365 62647370357858348343204137)
        ·
          refine ⟨46985527768393761257403103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62647370357858348343204137 46985527768393761257403103)
          ·
            refine ⟨70478291652590641886104655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46985527768393761257403103 70478291652590641886104655)
            ·
              refine ⟨105717437478885962829156983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70478291652590641886104655 105717437478885962829156983)
              ·
                refine ⟨158576156218328944243735475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105717437478885962829156983 158576156218328944243735475)
                ·
                  refine ⟨237864234327493416365603213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158576156218328944243735475 237864234327493416365603213)
                  ·
                    refine ⟨89199087872810031137101205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237864234327493416365603213 89199087872810031137101205)
                    ·
                      refine ⟨4181207244037970209551619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89199087872810031137101205 4181207244037970209551619)
                      ·
                        rfl

theorem cell23_8142872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_8142872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142872 prefixEnd_8142872 := by exact prefixLift 8142872
  have htrace : WordTrace (prefixWord ++ tailWord_8142872) baseStart_8142872 baseEnd_8142872 := by
    simpa [prefixWord, tailWord_8142872, baseEnd_8142872] using wordTrace_append hprefix tailTrace_8142872
  have hstable : (prefixWord ++ tailWord_8142872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142872).length < 2 ^ (prefixWord ++ tailWord_8142872).sum := by decide
  have hdescent : baseEnd_8142872 < baseStart_8142872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142876 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_8142876 : Nat := 118140960795 + 8142876 * 2 ^ 59
def prefixEnd_8142876 : Nat := 4983230072969 + 3 ^ 40 * 8142876 * 2
def baseEnd_8142876 : Nat := 4181209297960588193901601

theorem tailTrace_8142876 : CollatzResearch.WordTrace tailWord_8142876 prefixEnd_8142876 4181209297960588193901601 := by
  unfold tailWord_8142876
  simp only [CollatzResearch.WordTrace]
  refine ⟨148497543423879209673612241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197996724565172279564816321 148497543423879209673612241)
  ·
    refine ⟨111373157567909407255209181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148497543423879209673612241 111373157567909407255209181)
    ·
      refine ⟨41764934087966027720703443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111373157567909407255209181 41764934087966027720703443)
      ·
        refine ⟨62647401131949041581055165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41764934087966027720703443 62647401131949041581055165)
        ·
          refine ⟨23492775424480890592895687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62647401131949041581055165 23492775424480890592895687)
          ·
            refine ⟨35239163136721335889343531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23492775424480890592895687 35239163136721335889343531)
            ·
              refine ⟨52858744705082003834015297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35239163136721335889343531 52858744705082003834015297)
              ·
                refine ⟨39644058528811502875511473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52858744705082003834015297 39644058528811502875511473)
                ·
                  refine ⟨29733043896608627156633605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39644058528811502875511473 29733043896608627156633605)
                  ·
                    refine ⟨5574945730614117591868801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29733043896608627156633605 5574945730614117591868801)
                    ·
                      refine ⟨4181209297960588193901601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574945730614117591868801 4181209297960588193901601)
                      ·
                        rfl

theorem cell23_8142876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_8142876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142876 prefixEnd_8142876 := by exact prefixLift 8142876
  have htrace : WordTrace (prefixWord ++ tailWord_8142876) baseStart_8142876 baseEnd_8142876 := by
    simpa [prefixWord, tailWord_8142876, baseEnd_8142876] using wordTrace_append hprefix tailTrace_8142876
  have hstable : (prefixWord ++ tailWord_8142876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142876).length < 2 ^ (prefixWord ++ tailWord_8142876).sum := by decide
  have hdescent : baseEnd_8142876 < baseStart_8142876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142879 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_8142879 : Nat := 118140960795 + 8142879 * 2 ^ 59
def prefixEnd_8142879 : Nat := 4983230072969 + 3 ^ 40 * 8142879 * 2
def baseEnd_8142879 : Nat := 4181210838402551682164087

theorem tailTrace_8142879 : CollatzResearch.WordTrace tailWord_8142879 prefixEnd_8142879 4181210838402551682164087 := by
  unfold tailWord_8142879
  simp only [CollatzResearch.WordTrace]
  refine ⟨296995196266747550859583691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197996797511165033906389127 296995196266747550859583691)
  ·
    refine ⟨445492794400121326289375537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296995196266747550859583691 445492794400121326289375537)
    ·
      refine ⟨334119595800090994717031653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445492794400121326289375537 334119595800090994717031653)
      ·
        refine ⟨62647424212517061509443435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334119595800090994717031653 62647424212517061509443435)
        ·
          refine ⟨93971136318775592264165153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62647424212517061509443435 93971136318775592264165153)
          ·
            refine ⟨70478352239081694198123865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93971136318775592264165153 70478352239081694198123865)
            ·
              refine ⟨52858764179311270648592899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70478352239081694198123865 52858764179311270648592899)
              ·
                refine ⟨79288146268966905972889349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52858764179311270648592899 79288146268966905972889349)
                ·
                  refine ⟨14866527425431294869916753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79288146268966905972889349 14866527425431294869916753)
                  ·
                    refine ⟨11149895569073471152437565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14866527425431294869916753 11149895569073471152437565)
                    ·
                      refine ⟨4181210838402551682164087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11149895569073471152437565 4181210838402551682164087)
                      ·
                        rfl

theorem cell23_8142879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_8142879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142879 prefixEnd_8142879 := by exact prefixLift 8142879
  have htrace : WordTrace (prefixWord ++ tailWord_8142879) baseStart_8142879 baseEnd_8142879 := by
    simpa [prefixWord, tailWord_8142879, baseEnd_8142879] using wordTrace_append hprefix tailTrace_8142879
  have hstable : (prefixWord ++ tailWord_8142879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142879).length < 2 ^ (prefixWord ++ tailWord_8142879).sum := by decide
  have hdescent : baseEnd_8142879 < baseStart_8142879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142909 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_8142909 : Nat := 118140960795 + 8142909 * 2 ^ 59
def prefixEnd_8142909 : Nat := 4983230072969 + 3 ^ 40 * 8142909 * 2
def baseEnd_8142909 : Nat := 4181226242822186564788949

theorem tailTrace_8142909 : CollatzResearch.WordTrace tailWord_8142909 prefixEnd_8142909 4181226242822186564788949 := by
  unfold tailWord_8142909
  simp only [CollatzResearch.WordTrace]
  refine ⟨296996290456638865983175781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197997526971092577322117187 296996290456638865983175781)
  ·
    refine ⟨55686804460619787371845459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296996290456638865983175781 55686804460619787371845459)
    ·
      refine ⟨83530206690929681057768189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55686804460619787371845459 83530206690929681057768189)
      ·
        refine ⟨31323827509098630396663071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83530206690929681057768189 31323827509098630396663071)
        ·
          refine ⟨46985741263647945594994607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31323827509098630396663071 46985741263647945594994607)
          ·
            refine ⟨70478611895471918392491911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46985741263647945594994607 70478611895471918392491911)
            ·
              refine ⟨105717917843207877588737867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70478611895471918392491911 105717917843207877588737867)
              ·
                refine ⟨158576876764811816383106801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105717917843207877588737867 158576876764811816383106801)
                ·
                  refine ⟨118932657573608862287330101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158576876764811816383106801 118932657573608862287330101)
                  ·
                    refine ⟨11149936647525830839437197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118932657573608862287330101 11149936647525830839437197)
                    ·
                      refine ⟨4181226242822186564788949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11149936647525830839437197 4181226242822186564788949)
                      ·
                        rfl

theorem cell23_8142909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_8142909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142909 prefixEnd_8142909 := by exact prefixLift 8142909
  have htrace : WordTrace (prefixWord ++ tailWord_8142909) baseStart_8142909 baseEnd_8142909 := by
    simpa [prefixWord, tailWord_8142909, baseEnd_8142909] using wordTrace_append hprefix tailTrace_8142909
  have hstable : (prefixWord ++ tailWord_8142909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142909).length < 2 ^ (prefixWord ++ tailWord_8142909).sum := by decide
  have hdescent : baseEnd_8142909 < baseStart_8142909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142936 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 4, 3, 2]
def baseStart_8142936 : Nat := 118140960795 + 8142936 * 2 ^ 59
def prefixEnd_8142936 : Nat := 4983230072969 + 3 ^ 40 * 8142936 * 2
def baseEnd_8142936 : Nat := 4181240106799857959151325

theorem tailTrace_8142936 : CollatzResearch.WordTrace tailWord_8142936 prefixEnd_8142936 4181240106799857959151325 := by
  unfold tailWord_8142936
  simp only [CollatzResearch.WordTrace]
  refine ⟨148498637613770524797204331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197998183485027366396272441 148498637613770524797204331)
  ·
    refine ⟨222747956420655787195806497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148498637613770524797204331 222747956420655787195806497)
    ·
      refine ⟨167060967315491840396854873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222747956420655787195806497 167060967315491840396854873)
      ·
        refine ⟨125295725486618880297641155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167060967315491840396854873 125295725486618880297641155)
        ·
          refine ⟨187943588229928320446461733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125295725486618880297641155 187943588229928320446461733)
          ·
            refine ⟨35239422793111560083711575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187943588229928320446461733 35239422793111560083711575)
            ·
              refine ⟨52859134189667340125567363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35239422793111560083711575 52859134189667340125567363)
              ·
                refine ⟨79288701284501010188351045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52859134189667340125567363 79288701284501010188351045)
                ·
                  refine ⟨14866631490843939410315821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79288701284501010188351045 14866631490843939410315821)
                  ·
                    refine ⟨5574986809066477278868433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14866631490843939410315821 5574986809066477278868433)
                    ·
                      refine ⟨4181240106799857959151325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5574986809066477278868433 4181240106799857959151325)
                      ·
                        rfl

theorem cell23_8142936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_8142936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142936 prefixEnd_8142936 := by exact prefixLift 8142936
  have htrace : WordTrace (prefixWord ++ tailWord_8142936) baseStart_8142936 baseEnd_8142936 := by
    simpa [prefixWord, tailWord_8142936, baseEnd_8142936] using wordTrace_append hprefix tailTrace_8142936
  have hstable : (prefixWord ++ tailWord_8142936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142936).length < 2 ^ (prefixWord ++ tailWord_8142936).sum := by decide
  have hdescent : baseEnd_8142936 < baseStart_8142936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142979 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4]
def baseStart_8142979 : Nat := 118140960795 + 8142979 * 2 ^ 59
def prefixEnd_8142979 : Nat := 4983230072969 + 3 ^ 40 * 8142979 * 2
def baseEnd_8142979 : Nat := 4181262186468001290913627

theorem tailTrace_8142979 : CollatzResearch.WordTrace tailWord_8142979 prefixEnd_8142979 4181262186468001290913627 := by
  unfold tailWord_8142979
  simp only [CollatzResearch.WordTrace]
  refine ⟨296998843566385267938223991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197999229044256845292149327 296998843566385267938223991)
  ·
    refine ⟨445498265349577901907335987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296998843566385267938223991 445498265349577901907335987)
    ·
      refine ⟨668247398024366852861003981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445498265349577901907335987 668247398024366852861003981)
      ·
        refine ⟨250592774259137569822876493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668247398024366852861003981 250592774259137569822876493)
        ·
          refine ⟨93972290347176588683578685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250592774259137569822876493 93972290347176588683578685)
          ·
            refine ⟨35239608880191220756342007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93972290347176588683578685 35239608880191220756342007)
            ·
              refine ⟨52859413320286831134513011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35239608880191220756342007 52859413320286831134513011)
              ·
                refine ⟨79289119980430246701769517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52859413320286831134513011 79289119980430246701769517)
                ·
                  refine ⟨29733419992661342513163569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79289119980430246701769517 29733419992661342513163569)
                  ·
                    refine ⟨22300064994496006884872677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29733419992661342513163569 22300064994496006884872677)
                    ·
                      refine ⟨4181262186468001290913627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22300064994496006884872677 4181262186468001290913627)
                      ·
                        rfl

theorem cell23_8142979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_8142979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142979 prefixEnd_8142979 := by exact prefixLift 8142979
  have htrace : WordTrace (prefixWord ++ tailWord_8142979) baseStart_8142979 baseEnd_8142979 := by
    simpa [prefixWord, tailWord_8142979, baseEnd_8142979] using wordTrace_append hprefix tailTrace_8142979
  have hstable : (prefixWord ++ tailWord_8142979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142979).length < 2 ^ (prefixWord ++ tailWord_8142979).sum := by decide
  have hdescent : baseEnd_8142979 < baseStart_8142979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8142986 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_8142986 : Nat := 118140960795 + 8142986 * 2 ^ 59
def prefixEnd_8142986 : Nat := 4983230072969 + 3 ^ 40 * 8142986 * 2
def baseEnd_8142986 : Nat := 4181265780832582763526095

theorem tailTrace_8142986 : CollatzResearch.WordTrace tailWord_8142986 prefixEnd_8142986 4181265780832582763526095 := by
  unfold tailWord_8142986
  simp only [CollatzResearch.WordTrace]
  refine ⟨74249774719339977033432203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197999399251573272089152541 74249774719339977033432203)
  ·
    refine ⟨111374662079009965550148305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74249774719339977033432203 111374662079009965550148305)
    ·
      refine ⟨83530996559257474162611229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111374662079009965550148305 83530996559257474162611229)
      ·
        refine ⟨31324123709721552810979211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83530996559257474162611229 31324123709721552810979211)
        ·
          refine ⟨46986185564582329216468817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31324123709721552810979211 46986185564582329216468817)
          ·
            refine ⟨35239639173436746912351613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46986185564582329216468817 35239639173436746912351613)
            ·
              refine ⟨13214864690038780092131855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35239639173436746912351613 13214864690038780092131855)
              ·
                refine ⟨19822297035058170138197783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13214864690038780092131855 19822297035058170138197783)
                ·
                  refine ⟨29733445552587255207296675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19822297035058170138197783 29733445552587255207296675)
                  ·
                    refine ⟨44600168328880882810945013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29733445552587255207296675 44600168328880882810945013)
                    ·
                      refine ⟨4181265780832582763526095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44600168328880882810945013 4181265780832582763526095)
                      ·
                        rfl

theorem cell23_8142986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_8142986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8142986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8142986 prefixEnd_8142986 := by exact prefixLift 8142986
  have htrace : WordTrace (prefixWord ++ tailWord_8142986) baseStart_8142986 baseEnd_8142986 := by
    simpa [prefixWord, tailWord_8142986, baseEnd_8142986] using wordTrace_append hprefix tailTrace_8142986
  have hstable : (prefixWord ++ tailWord_8142986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8142986).length < 2 ^ (prefixWord ++ tailWord_8142986).sum := by decide
  have hdescent : baseEnd_8142986 < baseStart_8142986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8142986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143074 : List Nat := [3, 3, 4, 1, 2, 1, 2, 7]
def baseStart_8143074 : Nat := 118140960795 + 8143074 * 2 ^ 59
def prefixEnd_8143074 : Nat := 4983230072969 + 3 ^ 40 * 8143074 * 2
def baseEnd_8143074 : Nat := 154863369152969571082433

theorem tailTrace_8143074 : CollatzResearch.WordTrace tailWord_8143074 prefixEnd_8143074 154863369152969571082433 := by
  unfold tailWord_8143074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74250577125260274790733069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198001539000694066108621517 74250577125260274790733069)
  ·
    refine ⟨27843966421972603046524901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74250577125260274790733069 27843966421972603046524901)
    ·
      refine ⟨5220743704119863071223419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27843966421972603046524901 5220743704119863071223419)
      ·
        refine ⟨7831115556179794606835129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220743704119863071223419 7831115556179794606835129)
        ·
          refine ⟨5873336667134845955126347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7831115556179794606835129 5873336667134845955126347)
          ·
            refine ⟨8810005000702268932689521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873336667134845955126347 8810005000702268932689521)
            ·
              refine ⟨6607503750526701699517141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8810005000702268932689521 6607503750526701699517141)
              ·
                refine ⟨154863369152969571082433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6607503750526701699517141 154863369152969571082433)
                ·
                  rfl

theorem cell23_8143074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_8143074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143074 prefixEnd_8143074 := by exact prefixLift 8143074
  have htrace : WordTrace (prefixWord ++ tailWord_8143074) baseStart_8143074 baseEnd_8143074 := by
    simpa [prefixWord, tailWord_8143074, baseEnd_8143074] using wordTrace_append hprefix tailTrace_8143074
  have hstable : (prefixWord ++ tailWord_8143074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143074).length < 2 ^ (prefixWord ++ tailWord_8143074).sum := by decide
  have hdescent : baseEnd_8143074 < baseStart_8143074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143090 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_8143090 : Nat := 118140960795 + 8143090 * 2 ^ 59
def prefixEnd_8143090 : Nat := 4983230072969 + 3 ^ 40 * 8143090 * 2
def baseEnd_8143090 : Nat := 4181319182820650356625617

theorem tailTrace_8143090 : CollatzResearch.WordTrace tailWord_8143090 prefixEnd_8143090 4181319182820650356625617 := by
  unfold tailWord_8143090
  simp only [CollatzResearch.WordTrace]
  refine ⟨74250723017245783473878681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198001928045988755930343149 74250723017245783473878681)
  ·
    refine ⟨55688042262934337605409011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74250723017245783473878681 55688042262934337605409011)
    ·
      refine ⟨83532063394401506408113517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55688042262934337605409011 83532063394401506408113517)
      ·
        refine ⟨31324523772900564903042569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83532063394401506408113517 31324523772900564903042569)
        ·
          refine ⟨23493392829675423677281927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31324523772900564903042569 23493392829675423677281927)
          ·
            refine ⟨35240089244513135515922891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23493392829675423677281927 35240089244513135515922891)
            ·
              refine ⟨52860133866769703273884337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35240089244513135515922891 52860133866769703273884337)
              ·
                refine ⟨39645100400077277455413253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52860133866769703273884337 39645100400077277455413253)
                ·
                  refine ⟨7433456325014489522889985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39645100400077277455413253 7433456325014489522889985)
                  ·
                    refine ⟨5575092243760867142167489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433456325014489522889985 5575092243760867142167489)
                    ·
                      refine ⟨4181319182820650356625617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575092243760867142167489 4181319182820650356625617)
                      ·
                        rfl

theorem cell23_8143090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_8143090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143090 prefixEnd_8143090 := by exact prefixLift 8143090
  have htrace : WordTrace (prefixWord ++ tailWord_8143090) baseStart_8143090 baseEnd_8143090 := by
    simpa [prefixWord, tailWord_8143090, baseEnd_8143090] using wordTrace_append hprefix tailTrace_8143090
  have hstable : (prefixWord ++ tailWord_8143090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143090).length < 2 ^ (prefixWord ++ tailWord_8143090).sum := by decide
  have hdescent : baseEnd_8143090 < baseStart_8143090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143109 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_8143109 : Nat := 118140960795 + 8143109 * 2 ^ 59
def prefixEnd_8143109 : Nat := 4983230072969 + 3 ^ 40 * 8143109 * 2
def baseEnd_8143109 : Nat := 1393776312984361927429343

theorem tailTrace_8143109 : CollatzResearch.WordTrace tailWord_8143109 prefixEnd_8143109 1393776312984361927429343 := by
  unfold tailWord_8143109
  simp only [CollatzResearch.WordTrace]
  refine ⟨297003585055914300140456381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198002390037276200093637587 297003585055914300140456381)
  ·
    refine ⟨111376344395967862552671143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297003585055914300140456381 111376344395967862552671143)
    ·
      refine ⟨167064516593951793829006715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111376344395967862552671143 167064516593951793829006715)
      ·
        refine ⟨250596774890927690743510073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167064516593951793829006715 250596774890927690743510073)
        ·
          refine ⟨187947581168195768057632555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250596774890927690743510073 187947581168195768057632555)
          ·
            refine ⟨281921371752293652086448833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187947581168195768057632555 281921371752293652086448833)
            ·
              refine ⟨211441028814220239064836625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281921371752293652086448833 211441028814220239064836625)
              ·
                refine ⟨158580771610665179298627469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211441028814220239064836625 158580771610665179298627469)
                ·
                  refine ⟨59467789353999442236985301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158580771610665179298627469 59467789353999442236985301)
                  ·
                    refine ⟨1393776312984361927429343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59467789353999442236985301 1393776312984361927429343)
                    ·
                      rfl

theorem cell23_8143109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_8143109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143109 prefixEnd_8143109 := by exact prefixLift 8143109
  have htrace : WordTrace (prefixWord ++ tailWord_8143109) baseStart_8143109 baseEnd_8143109 := by
    simpa [prefixWord, tailWord_8143109, baseEnd_8143109] using wordTrace_append hprefix tailTrace_8143109
  have hstable : (prefixWord ++ tailWord_8143109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143109).length < 2 ^ (prefixWord ++ tailWord_8143109).sum := by decide
  have hdescent : baseEnd_8143109 < baseStart_8143109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143207 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 1, 4]
def baseStart_8143207 : Nat := 118140960795 + 8143207 * 2 ^ 59
def prefixEnd_8143207 : Nat := 4983230072969 + 3 ^ 40 * 8143207 * 2
def baseEnd_8143207 : Nat := 1393793086685742132954193

theorem tailTrace_8143207 : CollatzResearch.WordTrace tailWord_8143207 prefixEnd_8143207 1393793086685742132954193 := by
  unfold tailWord_8143207
  simp only [CollatzResearch.WordTrace]
  refine ⟨297007159409559262877523875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198004772939706175251682583 297007159409559262877523875)
  ·
    refine ⟨445510739114338894316285813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297007159409559262877523875 445510739114338894316285813)
    ·
      refine ⟨41766631791969271342151795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 445510739114338894316285813 41766631791969271342151795)
      ·
        refine ⟨62649947687953907013227693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41766631791969271342151795 62649947687953907013227693)
        ·
          refine ⟨23493730382982715129960385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62649947687953907013227693 23493730382982715129960385)
          ·
            refine ⟨17620297787237036347470289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23493730382982715129960385 17620297787237036347470289)
            ·
              refine ⟨13215223340427777260602717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17620297787237036347470289 13215223340427777260602717)
              ·
                refine ⟨4955708752660416472726019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13215223340427777260602717 4955708752660416472726019)
                ·
                  refine ⟨7433563128990624709089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955708752660416472726019 7433563128990624709089029)
                  ·
                    refine ⟨1393793086685742132954193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7433563128990624709089029 1393793086685742132954193)
                    ·
                      rfl

theorem cell23_8143207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_8143207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143207 prefixEnd_8143207 := by exact prefixLift 8143207
  have htrace : WordTrace (prefixWord ++ tailWord_8143207) baseStart_8143207 baseEnd_8143207 := by
    simpa [prefixWord, tailWord_8143207, baseEnd_8143207] using wordTrace_append hprefix tailTrace_8143207
  have hstable : (prefixWord ++ tailWord_8143207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143207).length < 2 ^ (prefixWord ++ tailWord_8143207).sum := by decide
  have hdescent : baseEnd_8143207 < baseStart_8143207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143253 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_8143253 : Nat := 118140960795 + 8143253 * 2 ^ 59
def prefixEnd_8143253 : Nat := 4983230072969 + 3 ^ 40 * 8143253 * 2
def baseEnd_8143253 : Nat := 4181402880167333218887367

theorem tailTrace_8143253 : CollatzResearch.WordTrace tailWord_8143253 prefixEnd_8143253 4181402880167333218887367 := by
  unfold tailWord_8143253
  simp only [CollatzResearch.WordTrace]
  refine ⟨297008837167392612733698413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198005891444928408489132275 297008837167392612733698413)
  ·
    refine ⟨111378313937772229775136905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297008837167392612733698413 111378313937772229775136905)
    ·
      refine ⟨83533735453329172331352679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111378313937772229775136905 83533735453329172331352679)
      ·
        refine ⟨125300603179993758497029019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83533735453329172331352679 125300603179993758497029019)
        ·
          refine ⟨187950904769990637745543529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125300603179993758497029019 187950904769990637745543529)
          ·
            refine ⟨140963178577492978309157647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187950904769990637745543529 140963178577492978309157647)
            ·
              refine ⟨211444767866239467463736471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140963178577492978309157647 211444767866239467463736471)
              ·
                refine ⟨317167151799359201195604707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211444767866239467463736471 317167151799359201195604707)
                ·
                  refine ⟨475750727699038801793407061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317167151799359201195604707 475750727699038801793407061)
                  ·
                    refine ⟨5575203840223110958516489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 475750727699038801793407061 5575203840223110958516489)
                    ·
                      refine ⟨4181402880167333218887367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575203840223110958516489 4181402880167333218887367)
                      ·
                        rfl

theorem cell23_8143253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_8143253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143253 prefixEnd_8143253 := by exact prefixLift 8143253
  have htrace : WordTrace (prefixWord ++ tailWord_8143253) baseStart_8143253 baseEnd_8143253 := by
    simpa [prefixWord, tailWord_8143253, baseEnd_8143253] using wordTrace_append hprefix tailTrace_8143253
  have hstable : (prefixWord ++ tailWord_8143253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143253).length < 2 ^ (prefixWord ++ tailWord_8143253).sum := by decide
  have hdescent : baseEnd_8143253 < baseStart_8143253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143263 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 6, 4]
def baseStart_8143263 : Nat := 118140960795 + 8143263 * 2 ^ 59
def prefixEnd_8143263 : Nat := 4983230072969 + 3 ^ 40 * 8143263 * 2
def baseEnd_8143263 : Nat := 1393802671657959393254107

theorem tailTrace_8143263 : CollatzResearch.WordTrace tailWord_8143263 prefixEnd_8143263 1393802671657959393254107 := by
  unfold tailWord_8143263
  simp only [CollatzResearch.WordTrace]
  refine ⟨297009201897356384441562443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198006134598237589627708295 297009201897356384441562443)
  ·
    refine ⟨445513802846034576662343665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297009201897356384441562443 445513802846034576662343665)
    ·
      refine ⟨334135352134525932496757749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445513802846034576662343665 334135352134525932496757749)
      ·
        refine ⟨31325189262611806171571039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334135352134525932496757749 31325189262611806171571039)
        ·
          refine ⟨46987783893917709257356559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31325189262611806171571039 46987783893917709257356559)
          ·
            refine ⟨70481675840876563886034839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46987783893917709257356559 70481675840876563886034839)
            ·
              refine ⟨105722513761314845829052259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70481675840876563886034839 105722513761314845829052259)
              ·
                refine ⟨158583770641972268743578389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105722513761314845829052259 158583770641972268743578389)
                ·
                  refine ⟨7433614248842450097355237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158583770641972268743578389 7433614248842450097355237)
                  ·
                    refine ⟨1393802671657959393254107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7433614248842450097355237 1393802671657959393254107)
                    ·
                      rfl

theorem cell23_8143263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_8143263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143263 prefixEnd_8143263 := by exact prefixLift 8143263
  have htrace : WordTrace (prefixWord ++ tailWord_8143263) baseStart_8143263 baseEnd_8143263 := by
    simpa [prefixWord, tailWord_8143263, baseEnd_8143263] using wordTrace_append hprefix tailTrace_8143263
  have hstable : (prefixWord ++ tailWord_8143263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143263).length < 2 ^ (prefixWord ++ tailWord_8143263).sum := by decide
  have hdescent : baseEnd_8143263 < baseStart_8143263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143264 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 1, 1, 3]
def baseStart_8143264 : Nat := 118140960795 + 8143264 * 2 ^ 59
def prefixEnd_8143264 : Nat := 4983230072969 + 3 ^ 40 * 8143264 * 2
def baseEnd_8143264 : Nat := 4181408528454532675849817

theorem tailTrace_8143264 : CollatzResearch.WordTrace tailWord_8143264 prefixEnd_8143264 4181408528454532675849817 := by
  unfold tailWord_8143264
  simp only [CollatzResearch.WordTrace]
  refine ⟨148504619185176380806174423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198006158913568507741565897 148504619185176380806174423)
  ·
    refine ⟨222756928777764571209261635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148504619185176380806174423 222756928777764571209261635)
    ·
      refine ⟨334135393166646856813892453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222756928777764571209261635 334135393166646856813892453)
      ·
        refine ⟨62650386218746285652604835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334135393166646856813892453 62650386218746285652604835)
        ·
          refine ⟨93975579328119428478907253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62650386218746285652604835 93975579328119428478907253)
          ·
            refine ⟨8810210562011196419897555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93975579328119428478907253 8810210562011196419897555)
            ·
              refine ⟨13215315843016794629846333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810210562011196419897555 13215315843016794629846333)
              ·
                refine ⟨4955743441131297986192375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13215315843016794629846333 4955743441131297986192375)
                ·
                  refine ⟨7433615161696946979288563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955743441131297986192375 7433615161696946979288563)
                  ·
                    refine ⟨11150422742545420468932845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7433615161696946979288563 11150422742545420468932845)
                    ·
                      refine ⟨4181408528454532675849817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11150422742545420468932845 4181408528454532675849817)
                      ·
                        rfl

theorem cell23_8143264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_8143264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143264 prefixEnd_8143264 := by exact prefixLift 8143264
  have htrace : WordTrace (prefixWord ++ tailWord_8143264) baseStart_8143264 baseEnd_8143264 := by
    simpa [prefixWord, tailWord_8143264, baseEnd_8143264] using wordTrace_append hprefix tailTrace_8143264
  have hstable : (prefixWord ++ tailWord_8143264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143264).length < 2 ^ (prefixWord ++ tailWord_8143264).sum := by decide
  have hdescent : baseEnd_8143264 < baseStart_8143264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143287 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 3, 2, 2]
def baseStart_8143287 : Nat := 118140960795 + 8143287 * 2 ^ 59
def prefixEnd_8143287 : Nat := 4983230072969 + 3 ^ 40 * 8143287 * 2
def baseEnd_8143287 : Nat := 4181420338509586085862211

theorem tailTrace_8143287 : CollatzResearch.WordTrace tailWord_8143287 prefixEnd_8143287 4181420338509586085862211 := by
  unfold tailWord_8143287
  simp only [CollatzResearch.WordTrace]
  refine ⟨297010077249269436540436115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198006718166179624360290743 297010077249269436540436115)
  ·
    refine ⟨445515115873904154810654173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297010077249269436540436115 445515115873904154810654173)
    ·
      refine ⟨167068168452714058053995315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445515115873904154810654173 167068168452714058053995315)
      ·
        refine ⟨250602252679071087080992973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167068168452714058053995315 250602252679071087080992973)
        ·
          refine ⟨93975844754651657655372365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250602252679071087080992973 93975844754651657655372365)
          ·
            refine ⟨35240941782994371620764637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93975844754651657655372365 35240941782994371620764637)
            ·
              refine ⟨13215353168622889357786739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35240941782994371620764637 13215353168622889357786739)
              ·
                refine ⟨19823029752934334036680109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215353168622889357786739 19823029752934334036680109)
                ·
                  refine ⟨7433636157350375263755041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19823029752934334036680109 7433636157350375263755041)
                  ·
                    refine ⟨5575227118012781447816281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433636157350375263755041 5575227118012781447816281)
                    ·
                      refine ⟨4181420338509586085862211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575227118012781447816281 4181420338509586085862211)
                      ·
                        rfl

theorem cell23_8143287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_8143287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143287 prefixEnd_8143287 := by exact prefixLift 8143287
  have htrace : WordTrace (prefixWord ++ tailWord_8143287) baseStart_8143287 baseEnd_8143287 := by
    simpa [prefixWord, tailWord_8143287, baseEnd_8143287] using wordTrace_append hprefix tailTrace_8143287
  have hstable : (prefixWord ++ tailWord_8143287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143287).length < 2 ^ (prefixWord ++ tailWord_8143287).sum := by decide
  have hdescent : baseEnd_8143287 < baseStart_8143287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143293 : List Nat := [1, 4, 1, 2, 2, 3, 2, 8]
def baseStart_8143293 : Nat := 118140960795 + 8143293 * 2 ^ 59
def prefixEnd_8143293 : Nat := 4983230072969 + 3 ^ 40 * 8143293 * 2
def baseEnd_8143293 : Nat := 154867534051611594903229

theorem tailTrace_8143293 : CollatzResearch.WordTrace tailWord_8143293 prefixEnd_8143293 154867534051611594903229 := by
  unfold tailWord_8143293
  simp only [CollatzResearch.WordTrace]
  refine ⟨297010296087247699565154533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198006864058165133043436355 297010296087247699565154533)
  ·
    refine ⟨55689430516358943668466475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297010296087247699565154533 55689430516358943668466475)
    ·
      refine ⟨83534145774538415502699713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55689430516358943668466475 83534145774538415502699713)
      ·
        refine ⟨62650609330903811627024785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83534145774538415502699713 62650609330903811627024785)
        ·
          refine ⟨46987956998177858720268589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62650609330903811627024785 46987956998177858720268589)
          ·
            refine ⟨17620483874316697020100721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46987956998177858720268589 17620483874316697020100721)
            ·
              refine ⟨13215362905737522765075541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17620483874316697020100721 13215362905737522765075541)
              ·
                refine ⟨154867534051611594903229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13215362905737522765075541 154867534051611594903229)
                ·
                  rfl

theorem cell23_8143293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 8].length) (baseStart_8143293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143293 prefixEnd_8143293 := by exact prefixLift 8143293
  have htrace : WordTrace (prefixWord ++ tailWord_8143293) baseStart_8143293 baseEnd_8143293 := by
    simpa [prefixWord, tailWord_8143293, baseEnd_8143293] using wordTrace_append hprefix tailTrace_8143293
  have hstable : (prefixWord ++ tailWord_8143293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143293).length < 2 ^ (prefixWord ++ tailWord_8143293).sum := by decide
  have hdescent : baseEnd_8143293 < baseStart_8143293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143296 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_8143296 : Nat := 118140960795 + 8143296 * 2 ^ 59
def prefixEnd_8143296 : Nat := 4983230072969 + 3 ^ 40 * 8143296 * 2
def baseEnd_8143296 : Nat := 4181424959835476550649669

theorem tailTrace_8143296 : CollatzResearch.WordTrace tailWord_8143296 prefixEnd_8143296 4181424959835476550649669 := by
  unfold tailWord_8143296
  simp only [CollatzResearch.WordTrace]
  refine ⟨148505202753118415538756871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198006937004157887385009161 148505202753118415538756871)
  ·
    refine ⟨222757804129677623308135307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148505202753118415538756871 222757804129677623308135307)
    ·
      refine ⟨334136706194516434962202961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222757804129677623308135307 334136706194516434962202961)
      ·
        refine ⟨250602529645887326221652221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334136706194516434962202961 250602529645887326221652221)
        ·
          refine ⟨93975948617207747333119583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250602529645887326221652221 93975948617207747333119583)
          ·
            refine ⟨140963922925811620999679375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93975948617207747333119583 140963922925811620999679375)
            ·
              refine ⟨211445884388717431499519063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140963922925811620999679375 211445884388717431499519063)
              ·
                refine ⟨317168826583076147249278595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211445884388717431499519063 317168826583076147249278595)
                ·
                  refine ⟨475753239874614220873917893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317168826583076147249278595 475753239874614220873917893)
                  ·
                    refine ⟨89203732476490166413859605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475753239874614220873917893 89203732476490166413859605)
                    ·
                      refine ⟨4181424959835476550649669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89203732476490166413859605 4181424959835476550649669)
                      ·
                        rfl

theorem cell23_8143296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_8143296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143296 prefixEnd_8143296 := by exact prefixLift 8143296
  have htrace : WordTrace (prefixWord ++ tailWord_8143296) baseStart_8143296 baseEnd_8143296 := by
    simpa [prefixWord, tailWord_8143296, baseEnd_8143296] using wordTrace_append hprefix tailTrace_8143296
  have hstable : (prefixWord ++ tailWord_8143296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143296).length < 2 ^ (prefixWord ++ tailWord_8143296).sum := by decide
  have hdescent : baseEnd_8143296 < baseStart_8143296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143338 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_8143338 : Nat := 118140960795 + 8143338 * 2 ^ 59
def prefixEnd_8143338 : Nat := 4983230072969 + 3 ^ 40 * 8143338 * 2
def baseEnd_8143338 : Nat := 4181446526022965386324477

theorem tailTrace_8143338 : CollatzResearch.WordTrace tailWord_8143338 prefixEnd_8143338 4181446526022965386324477 := by
  unfold tailWord_8143338
  simp only [CollatzResearch.WordTrace]
  refine ⟨74252984343021168062635667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198007958248056448167028445 74252984343021168062635667)
  ·
    refine ⟨111379476514531752093953501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74252984343021168062635667 111379476514531752093953501)
    ·
      refine ⟨41767303692949407035232563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111379476514531752093953501 41767303692949407035232563)
      ·
        refine ⟨62650955539424110552848845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41767303692949407035232563 62650955539424110552848845)
        ·
          refine ⟨23494108327284041457318317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62650955539424110552848845 23494108327284041457318317)
          ·
            refine ⟨8810290622731515546494369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23494108327284041457318317 8810290622731515546494369)
            ·
              refine ⟨6607717967048636659870777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8810290622731515546494369 6607717967048636659870777)
              ·
                refine ⟨4955788475286477494903083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607717967048636659870777 4955788475286477494903083)
                ·
                  refine ⟨7433682712929716242354625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955788475286477494903083 7433682712929716242354625)
                  ·
                    refine ⟨5575262034697287181765969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433682712929716242354625 5575262034697287181765969)
                    ·
                      refine ⟨4181446526022965386324477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575262034697287181765969 4181446526022965386324477)
                      ·
                        rfl

theorem cell23_8143338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_8143338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143338 prefixEnd_8143338 := by exact prefixLift 8143338
  have htrace : WordTrace (prefixWord ++ tailWord_8143338) baseStart_8143338 baseEnd_8143338 := by
    simpa [prefixWord, tailWord_8143338, baseEnd_8143338] using wordTrace_append hprefix tailTrace_8143338
  have hstable : (prefixWord ++ tailWord_8143338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143338).length < 2 ^ (prefixWord ++ tailWord_8143338).sum := by decide
  have hdescent : baseEnd_8143338 < baseStart_8143338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143363 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 3]
def baseStart_8143363 : Nat := 118140960795 + 8143363 * 2 ^ 59
def prefixEnd_8143363 : Nat := 4983230072969 + 3 ^ 40 * 8143363 * 2
def baseEnd_8143363 : Nat := 4181459363039327788511861

theorem tailTrace_8143363 : CollatzResearch.WordTrace tailWord_8143363 prefixEnd_8143363 4181459363039327788511861 := by
  unfold tailWord_8143363
  simp only [CollatzResearch.WordTrace]
  refine ⟨297012849196994101520202743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198008566131329401013468495 297012849196994101520202743)
  ·
    refine ⟨445519273795491152280304115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297012849196994101520202743 445519273795491152280304115)
    ·
      refine ⟨668278910693236728420456173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445519273795491152280304115 668278910693236728420456173)
      ·
        refine ⟨250604591509963773157671065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668278910693236728420456173 250604591509963773157671065)
        ·
          refine ⟨187953443632472829868253299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250604591509963773157671065 187953443632472829868253299)
          ·
            refine ⟨281930165448709244802379949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187953443632472829868253299 281930165448709244802379949)
            ·
              refine ⟨105723812043265966800892481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281930165448709244802379949 105723812043265966800892481)
              ·
                refine ⟨79292859032449475100669361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105723812043265966800892481 79292859032449475100669361)
                ·
                  refine ⟨59469644274337106325502021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79292859032449475100669361 59469644274337106325502021)
                  ·
                    refine ⟨11150558301438207436031629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59469644274337106325502021 11150558301438207436031629)
                    ·
                      refine ⟨4181459363039327788511861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11150558301438207436031629 4181459363039327788511861)
                      ·
                        rfl

theorem cell23_8143363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_8143363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143363 prefixEnd_8143363 := by exact prefixLift 8143363
  have htrace : WordTrace (prefixWord ++ tailWord_8143363) baseStart_8143363 baseEnd_8143363 := by
    simpa [prefixWord, tailWord_8143363, baseEnd_8143363] using wordTrace_append hprefix tailTrace_8143363
  have hstable : (prefixWord ++ tailWord_8143363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143363).length < 2 ^ (prefixWord ++ tailWord_8143363).sum := by decide
  have hdescent : baseEnd_8143363 < baseStart_8143363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143400 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 7]
def baseStart_8143400 : Nat := 118140960795 + 8143400 * 2 ^ 59
def prefixEnd_8143400 : Nat := 4983230072969 + 3 ^ 40 * 8143400 * 2
def baseEnd_8143400 : Nat := 464608706869282682638799

theorem tailTrace_8143400 : CollatzResearch.WordTrace tailWord_8143400 prefixEnd_8143400 464608706869282682638799 := by
  unfold tailWord_8143400
  simp only [CollatzResearch.WordTrace]
  refine ⟨148507099348930028419649827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198009465798573371226199769 148507099348930028419649827)
  ·
    refine ⟨222760649023395042629474741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148507099348930028419649827 222760649023395042629474741)
    ·
      refine ⟨20883810845943285246513257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222760649023395042629474741 20883810845943285246513257)
      ·
        refine ⟨15662858134457463934884943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20883810845943285246513257 15662858134457463934884943)
        ·
          refine ⟨23494287201686195902327415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15662858134457463934884943 23494287201686195902327415)
          ·
            refine ⟨35241430802529293853491123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23494287201686195902327415 35241430802529293853491123)
            ·
              refine ⟨52862146203793940780236685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35241430802529293853491123 52862146203793940780236685)
              ·
                refine ⟨19823304826422727792588757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52862146203793940780236685 19823304826422727792588757)
                ·
                  refine ⟨464608706869282682638799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19823304826422727792588757 464608706869282682638799)
                  ·
                    rfl

theorem cell23_8143400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_8143400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143400 prefixEnd_8143400 := by exact prefixLift 8143400
  have htrace : WordTrace (prefixWord ++ tailWord_8143400) baseStart_8143400 baseEnd_8143400 := by
    simpa [prefixWord, tailWord_8143400, baseEnd_8143400] using wordTrace_append hprefix tailTrace_8143400
  have hstable : (prefixWord ++ tailWord_8143400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143400).length < 2 ^ (prefixWord ++ tailWord_8143400).sum := by decide
  have hdescent : baseEnd_8143400 < baseStart_8143400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143405 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8143405 : Nat := 118140960795 + 8143405 * 2 ^ 59
def prefixEnd_8143405 : Nat := 4983230072969 + 3 ^ 40 * 8143405 * 2
def baseEnd_8143405 : Nat := 4181480929226816624186669

theorem tailTrace_8143405 : CollatzResearch.WordTrace tailWord_8143405 prefixEnd_8143405 4181480929226816624186669 := by
  unfold tailWord_8143405
  simp only [CollatzResearch.WordTrace]
  refine ⟨297014381062841942693231669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198009587375227961795487779 297014381062841942693231669)
  ·
    refine ⟨27845098224641432127490469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297014381062841942693231669 27845098224641432127490469)
    ·
      refine ⟨5220955917120268523904463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27845098224641432127490469 5220955917120268523904463)
      ·
        refine ⟨7831433875680402785856695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220955917120268523904463 7831433875680402785856695)
        ·
          refine ⟨11747150813520604178785043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7831433875680402785856695 11747150813520604178785043)
          ·
            refine ⟨17620726220280906268177565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11747150813520604178785043 17620726220280906268177565)
            ·
              refine ⟨6607772332605339850566587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17620726220280906268177565 6607772332605339850566587)
              ·
                refine ⟨9911658498908009775849881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607772332605339850566587 9911658498908009775849881)
                ·
                  refine ⟨7433743874181007331887411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9911658498908009775849881 7433743874181007331887411)
                  ·
                    refine ⟨11150615811271510997831117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7433743874181007331887411 11150615811271510997831117)
                    ·
                      refine ⟨4181480929226816624186669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11150615811271510997831117 4181480929226816624186669)
                      ·
                        rfl

theorem cell23_8143405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8143405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143405 prefixEnd_8143405 := by exact prefixLift 8143405
  have htrace : WordTrace (prefixWord ++ tailWord_8143405) baseStart_8143405 baseEnd_8143405 := by
    simpa [prefixWord, tailWord_8143405, baseEnd_8143405] using wordTrace_append hprefix tailTrace_8143405
  have hstable : (prefixWord ++ tailWord_8143405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143405).length < 2 ^ (prefixWord ++ tailWord_8143405).sum := by decide
  have hdescent : baseEnd_8143405 < baseStart_8143405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143410 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_8143410 : Nat := 118140960795 + 8143410 * 2 ^ 59
def prefixEnd_8143410 : Nat := 4983230072969 + 3 ^ 40 * 8143410 * 2
def baseEnd_8143410 : Nat := 4181483496630089104624145

theorem tailTrace_8143410 : CollatzResearch.WordTrace tailWord_8143410 prefixEnd_8143410 4181483496630089104624145 := by
  unfold tailWord_8143410
  simp only [CollatzResearch.WordTrace]
  refine ⟨74253640856955957136790921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198009708951882552364775789 74253640856955957136790921)
  ·
    refine ⟨55690230642716967852593191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74253640856955957136790921 55690230642716967852593191)
    ·
      refine ⟨83535345964075451778889787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55690230642716967852593191 83535345964075451778889787)
      ·
        refine ⟨125303018946113177668334681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83535345964075451778889787 125303018946113177668334681)
        ·
          refine ⟨93977264209584883251251011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125303018946113177668334681 93977264209584883251251011)
          ·
            refine ⟨140965896314377324876876517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93977264209584883251251011 140965896314377324876876517)
            ·
              refine ⟨26431105558945748414414347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140965896314377324876876517 26431105558945748414414347)
              ·
                refine ⟨39646658338418622621621521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26431105558945748414414347 39646658338418622621621521)
                ·
                  refine ⟨29734993753813966966216141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39646658338418622621621521 29734993753813966966216141)
                  ·
                    refine ⟨11150622657680237612331053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29734993753813966966216141 11150622657680237612331053)
                    ·
                      refine ⟨4181483496630089104624145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11150622657680237612331053 4181483496630089104624145)
                      ·
                        rfl

theorem cell23_8143410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_8143410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143410 prefixEnd_8143410 := by exact prefixLift 8143410
  have htrace : WordTrace (prefixWord ++ tailWord_8143410) baseStart_8143410 baseEnd_8143410 := by
    simpa [prefixWord, tailWord_8143410, baseEnd_8143410] using wordTrace_append hprefix tailTrace_8143410
  have hstable : (prefixWord ++ tailWord_8143410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143410).length < 2 ^ (prefixWord ++ tailWord_8143410).sum := by decide
  have hdescent : baseEnd_8143410 < baseStart_8143410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143413 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_8143413 : Nat := 118140960795 + 8143413 * 2 ^ 59
def prefixEnd_8143413 : Nat := 4983230072969 + 3 ^ 40 * 8143413 * 2
def baseEnd_8143413 : Nat := 1393828345690684197628877

theorem tailTrace_8143413 : CollatzResearch.WordTrace tailWord_8143413 prefixEnd_8143413 1393828345690684197628877 := by
  unfold tailWord_8143413
  simp only [CollatzResearch.WordTrace]
  refine ⟨297014672846812960059522893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198009781897875306706348595 297014672846812960059522893)
  ·
    refine ⟨111380502317554860022321085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297014672846812960059522893 111380502317554860022321085)
    ·
      refine ⟨41767688369083072508370407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111380502317554860022321085 41767688369083072508370407)
      ·
        refine ⟨62651532553624608762555611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41767688369083072508370407 62651532553624608762555611)
        ·
          refine ⟨93977298830436913143833417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62651532553624608762555611 93977298830436913143833417)
          ·
            refine ⟨70482974122827684857875063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93977298830436913143833417 70482974122827684857875063)
            ·
              refine ⟨105724461184241527286812595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70482974122827684857875063 105724461184241527286812595)
              ·
                refine ⟨158586691776362290930218893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105724461184241527286812595 158586691776362290930218893)
                ·
                  refine ⟨59470009416135859098832085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158586691776362290930218893 59470009416135859098832085)
                  ·
                    refine ⟨1393828345690684197628877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59470009416135859098832085 1393828345690684197628877)
                    ·
                      rfl

theorem cell23_8143413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_8143413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143413 prefixEnd_8143413 := by exact prefixLift 8143413
  have htrace : WordTrace (prefixWord ++ tailWord_8143413) baseStart_8143413 baseEnd_8143413 := by
    simpa [prefixWord, tailWord_8143413, baseEnd_8143413] using wordTrace_append hprefix tailTrace_8143413
  have hstable : (prefixWord ++ tailWord_8143413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143413).length < 2 ^ (prefixWord ++ tailWord_8143413).sum := by decide
  have hdescent : baseEnd_8143413 < baseStart_8143413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143551 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 1, 1, 3]
def baseStart_8143551 : Nat := 118140960795 + 8143551 * 2 ^ 59
def prefixEnd_8143551 : Nat := 4983230072969 + 3 ^ 40 * 8143551 * 2
def baseEnd_8143551 : Nat := 4181555897402373052960997

theorem tailTrace_8143551 : CollatzResearch.WordTrace tailWord_8143551 prefixEnd_8143551 4181555897402373052960997 := by
  unfold tailWord_8143551
  simp only [CollatzResearch.WordTrace]
  refine ⟨297019706120313009628046507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198013137413542006418697671 297019706120313009628046507)
  ·
    refine ⟨445529559180469514442069761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297019706120313009628046507 445529559180469514442069761)
    ·
      refine ⟨334147169385352135831552321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445529559180469514442069761 334147169385352135831552321)
      ·
        refine ⟨250610377039014101873664241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334147169385352135831552321 250610377039014101873664241)
        ·
          refine ⟨187957782779260576405248181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250610377039014101873664241 187957782779260576405248181)
          ·
            refine ⟨17621042135555679037992017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187957782779260576405248181 17621042135555679037992017)
            ·
              refine ⟨13215781601666759278494013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17621042135555679037992017 13215781601666759278494013)
              ·
                refine ⟨4955918100625034729435255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13215781601666759278494013 4955918100625034729435255)
                ·
                  refine ⟨7433877150937552094152883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955918100625034729435255 7433877150937552094152883)
                  ·
                    refine ⟨11150815726406328141229325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7433877150937552094152883 11150815726406328141229325)
                    ·
                      refine ⟨4181555897402373052960997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11150815726406328141229325 4181555897402373052960997)
                      ·
                        rfl

theorem cell23_8143551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_8143551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143551 prefixEnd_8143551 := by exact prefixLift 8143551
  have htrace : WordTrace (prefixWord ++ tailWord_8143551) baseStart_8143551 baseEnd_8143551 := by
    simpa [prefixWord, tailWord_8143551, baseEnd_8143551] using wordTrace_append hprefix tailTrace_8143551
  have hstable : (prefixWord ++ tailWord_8143551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143551).length < 2 ^ (prefixWord ++ tailWord_8143551).sum := by decide
  have hdescent : baseEnd_8143551 < baseStart_8143551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143558 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_8143558 : Nat := 118140960795 + 8143558 * 2 ^ 59
def prefixEnd_8143558 : Nat := 4983230072969 + 3 ^ 40 * 8143558 * 2
def baseEnd_8143558 : Nat := 464617721307439391730385

theorem tailTrace_8143558 : CollatzResearch.WordTrace tailWord_8143558 prefixEnd_8143558 464617721307439391730385 := by
  unfold tailWord_8143558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9281873794727739056985979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198013307620858433215700885 9281873794727739056985979)
  ·
    refine ⟨13922810692091608585478969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9281873794727739056985979 13922810692091608585478969)
    ·
      refine ⟨10442108019068706439109227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13922810692091608585478969 10442108019068706439109227)
      ·
        refine ⟨15663162028603059658663841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442108019068706439109227 15663162028603059658663841)
        ·
          refine ⟨11747371521452294743997881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15663162028603059658663841 11747371521452294743997881)
          ·
            refine ⟨8810528641089221057998411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11747371521452294743997881 8810528641089221057998411)
            ·
              refine ⟨13215792961633831586997617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810528641089221057998411 13215792961633831586997617)
              ·
                refine ⟨9911844721225373690248213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13215792961633831586997617 9911844721225373690248213)
                ·
                  refine ⟨464617721307439391730385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9911844721225373690248213 464617721307439391730385)
                  ·
                    rfl

theorem cell23_8143558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_8143558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143558 prefixEnd_8143558 := by exact prefixLift 8143558
  have htrace : WordTrace (prefixWord ++ tailWord_8143558) baseStart_8143558 baseEnd_8143558 := by
    simpa [prefixWord, tailWord_8143558, baseEnd_8143558] using wordTrace_append hprefix tailTrace_8143558
  have hstable : (prefixWord ++ tailWord_8143558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143558).length < 2 ^ (prefixWord ++ tailWord_8143558).sum := by decide
  have hdescent : baseEnd_8143558 < baseStart_8143558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143587 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 6]
def baseStart_8143587 : Nat := 118140960795 + 8143587 * 2 ^ 59
def prefixEnd_8143587 : Nat := 4983230072969 + 3 ^ 40 * 8143587 * 2
def baseEnd_8143587 : Nat := 4181574382705934912110831

theorem tailTrace_8143587 : CollatzResearch.WordTrace tailWord_8143587 prefixEnd_8143587 4181574382705934912110831 := by
  unfold tailWord_8143587
  simp only [CollatzResearch.WordTrace]
  refine ⟨297021019148182587776357015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198014012765455058517571343 297021019148182587776357015)
  ·
    refine ⟨445531528722273881664535523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297021019148182587776357015 445531528722273881664535523)
    ·
      refine ⟨668297293083410822496803285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445531528722273881664535523 668297293083410822496803285)
      ·
        refine ⟨15663217806642441152268827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 668297293083410822496803285 15663217806642441152268827)
        ·
          refine ⟨23494826709963661728403241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663217806642441152268827 23494826709963661728403241)
          ·
            refine ⟨17621120032472746296302431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23494826709963661728403241 17621120032472746296302431)
            ·
              refine ⟨26431680048709119444453647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17621120032472746296302431 26431680048709119444453647)
              ·
                refine ⟨39647520073063679166680471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26431680048709119444453647 39647520073063679166680471)
                ·
                  refine ⟨59471280109595518750020707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39647520073063679166680471 59471280109595518750020707)
                  ·
                    refine ⟨89206920164393278125031061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59471280109595518750020707 89206920164393278125031061)
                    ·
                      refine ⟨4181574382705934912110831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89206920164393278125031061 4181574382705934912110831)
                      ·
                        rfl

theorem cell23_8143587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_8143587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143587 prefixEnd_8143587 := by exact prefixLift 8143587
  have htrace : WordTrace (prefixWord ++ tailWord_8143587) baseStart_8143587 baseEnd_8143587 := by
    simpa [prefixWord, tailWord_8143587, baseEnd_8143587] using wordTrace_append hprefix tailTrace_8143587
  have hstable : (prefixWord ++ tailWord_8143587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143587).length < 2 ^ (prefixWord ++ tailWord_8143587).sum := by decide
  have hdescent : baseEnd_8143587 < baseStart_8143587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143624 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_8143624 : Nat := 118140960795 + 8143624 * 2 ^ 59
def prefixEnd_8143624 : Nat := 4983230072969 + 3 ^ 40 * 8143624 * 2
def baseEnd_8143624 : Nat := 4181593381490151267348161

theorem tailTrace_8143624 : CollatzResearch.WordTrace tailWord_8143624 prefixEnd_8143624 4181593381490151267348161 := by
  unfold tailWord_8143624
  simp only [CollatzResearch.WordTrace]
  refine ⟨148511184324524271547726963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198014912432699028730302617 148511184324524271547726963)
  ·
    refine ⟨222766776486786407321590445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148511184324524271547726963 222766776486786407321590445)
    ·
      refine ⟨83537541182544902745596417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222766776486786407321590445 83537541182544902745596417)
      ·
        refine ⟨62653155886908677059197313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83537541182544902745596417 62653155886908677059197313)
        ·
          refine ⟨46989866915181507794397985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62653155886908677059197313 46989866915181507794397985)
          ·
            refine ⟨35242400186386130845798489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46989866915181507794397985 35242400186386130845798489)
            ·
              refine ⟨26431800139789598134348867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35242400186386130845798489 26431800139789598134348867)
              ·
                refine ⟨39647700209684397201523301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26431800139789598134348867 39647700209684397201523301)
                ·
                  refine ⟨7433943789315824475285619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39647700209684397201523301 7433943789315824475285619)
                  ·
                    refine ⟨11150915683973736712928429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7433943789315824475285619 11150915683973736712928429)
                    ·
                      refine ⟨4181593381490151267348161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11150915683973736712928429 4181593381490151267348161)
                      ·
                        rfl

theorem cell23_8143624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_8143624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143624 prefixEnd_8143624 := by exact prefixLift 8143624
  have htrace : WordTrace (prefixWord ++ tailWord_8143624) baseStart_8143624 baseEnd_8143624 := by
    simpa [prefixWord, tailWord_8143624, baseEnd_8143624] using wordTrace_append hprefix tailTrace_8143624
  have hstable : (prefixWord ++ tailWord_8143624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143624).length < 2 ^ (prefixWord ++ tailWord_8143624).sum := by decide
  have hdescent : baseEnd_8143624 < baseStart_8143624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143640 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_8143640 : Nat := 118140960795 + 8143640 * 2 ^ 59
def prefixEnd_8143640 : Nat := 4983230072969 + 3 ^ 40 * 8143640 * 2
def baseEnd_8143640 : Nat := 1393867199060207734916029

theorem tailTrace_8143640 : CollatzResearch.WordTrace tailWord_8143640 prefixEnd_8143640 1393867199060207734916029 := by
  unfold tailWord_8143640
  simp only [CollatzResearch.WordTrace]
  refine ⟨148511476108495288914018187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198015301477993718552024249 148511476108495288914018187)
  ·
    refine ⟨222767214162742933371027281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148511476108495288914018187 222767214162742933371027281)
    ·
      refine ⟨167075410622057200028270461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222767214162742933371027281 167075410622057200028270461)
      ·
        refine ⟨62653278983271450010601423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167075410622057200028270461 62653278983271450010601423)
        ·
          refine ⟨93979918474907175015902135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62653278983271450010601423 93979918474907175015902135)
          ·
            refine ⟨140969877712360762523853203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93979918474907175015902135 140969877712360762523853203)
            ·
              refine ⟨211454816568541143785779805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140969877712360762523853203 211454816568541143785779805)
              ·
                refine ⟨79295556213202928919667427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211454816568541143785779805 79295556213202928919667427)
                ·
                  refine ⟨118943334319804393379501141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79295556213202928919667427 118943334319804393379501141)
                  ·
                    refine ⟨1393867199060207734916029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118943334319804393379501141 1393867199060207734916029)
                    ·
                      rfl

theorem cell23_8143640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_8143640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143640 prefixEnd_8143640 := by exact prefixLift 8143640
  have htrace : WordTrace (prefixWord ++ tailWord_8143640) baseStart_8143640 baseEnd_8143640 := by
    simpa [prefixWord, tailWord_8143640, baseEnd_8143640] using wordTrace_append hprefix tailTrace_8143640
  have hstable : (prefixWord ++ tailWord_8143640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143640).length < 2 ^ (prefixWord ++ tailWord_8143640).sum := by decide
  have hdescent : baseEnd_8143640 < baseStart_8143640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143645 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_8143645 : Nat := 118140960795 + 8143645 * 2 ^ 59
def prefixEnd_8143645 : Nat := 4983230072969 + 3 ^ 40 * 8143645 * 2
def baseEnd_8143645 : Nat := 4181604164583895685185565

theorem tailTrace_8143645 : CollatzResearch.WordTrace tailWord_8143645 prefixEnd_8143645 4181604164583895685185565 := by
  unfold tailWord_8143645
  simp only [CollatzResearch.WordTrace]
  refine ⟨297023134581972463681968389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198015423054648309121312259 297023134581972463681968389)
  ·
    refine ⟨55691837734119836940369073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297023134581972463681968389 55691837734119836940369073)
    ·
      refine ⟨41768878300589877705276805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55691837734119836940369073 41768878300589877705276805)
      ·
        refine ⟨7831664681360602069739401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41768878300589877705276805 7831664681360602069739401)
        ·
          refine ⟨5873748511020451552304551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7831664681360602069739401 5873748511020451552304551)
          ·
            refine ⟨8810622766530677328456827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873748511020451552304551 8810622766530677328456827)
            ·
              refine ⟨13215934149796015992685241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810622766530677328456827 13215934149796015992685241)
              ·
                refine ⟨9911950612347011994513931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13215934149796015992685241 9911950612347011994513931)
                ·
                  refine ⟨14867925918520517991770897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9911950612347011994513931 14867925918520517991770897)
                  ·
                    refine ⟨11150944438890388493828173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14867925918520517991770897 11150944438890388493828173)
                    ·
                      refine ⟨4181604164583895685185565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11150944438890388493828173 4181604164583895685185565)
                      ·
                        rfl

theorem cell23_8143645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_8143645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143645 prefixEnd_8143645 := by exact prefixLift 8143645
  have htrace : WordTrace (prefixWord ++ tailWord_8143645) baseStart_8143645 baseEnd_8143645 := by
    simpa [prefixWord, tailWord_8143645, baseEnd_8143645] using wordTrace_append hprefix tailTrace_8143645
  have hstable : (prefixWord ++ tailWord_8143645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143645).length < 2 ^ (prefixWord ++ tailWord_8143645).sum := by decide
  have hdescent : baseEnd_8143645 < baseStart_8143645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143664 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 6, 2, 2]
def baseStart_8143664 : Nat := 118140960795 + 8143664 * 2 ^ 59
def prefixEnd_8143664 : Nat := 4983230072969 + 3 ^ 40 * 8143664 * 2
def baseEnd_8143664 : Nat := 4181613920716331110847977

theorem tailTrace_8143664 : CollatzResearch.WordTrace tailWord_8143664 prefixEnd_8143664 4181613920716331110847977 := by
  unfold tailWord_8143664
  simp only [CollatzResearch.WordTrace]
  refine ⟨148511913784451814963455023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198015885045935753284606697 148511913784451814963455023)
  ·
    refine ⟨222767870676677722445182535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148511913784451814963455023 222767870676677722445182535)
    ·
      refine ⟨334151806015016583667773803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222767870676677722445182535 334151806015016583667773803)
      ·
        refine ⟨501227709022524875501660705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334151806015016583667773803 501227709022524875501660705)
        ·
          refine ⟨375920781766893656626245529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501227709022524875501660705 375920781766893656626245529)
          ·
            refine ⟨281940586325170242469684147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375920781766893656626245529 281940586325170242469684147)
            ·
              refine ⟨422910879487755363704526221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281940586325170242469684147 422910879487755363704526221)
              ·
                refine ⟨158591579807908261389197333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422910879487755363704526221 158591579807908261389197333)
                ·
                  refine ⟨7433980303495699752618625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158591579807908261389197333 7433980303495699752618625)
                  ·
                    refine ⟨5575485227621774814463969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433980303495699752618625 5575485227621774814463969)
                    ·
                      refine ⟨4181613920716331110847977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575485227621774814463969 4181613920716331110847977)
                      ·
                        rfl

theorem cell23_8143664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 2, 2].length) (baseStart_8143664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143664 prefixEnd_8143664 := by exact prefixLift 8143664
  have htrace : WordTrace (prefixWord ++ tailWord_8143664) baseStart_8143664 baseEnd_8143664 := by
    simpa [prefixWord, tailWord_8143664, baseEnd_8143664] using wordTrace_append hprefix tailTrace_8143664
  have hstable : (prefixWord ++ tailWord_8143664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143664).length < 2 ^ (prefixWord ++ tailWord_8143664).sum := by decide
  have hdescent : baseEnd_8143664 < baseStart_8143664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143667 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5]
def baseStart_8143667 : Nat := 118140960795 + 8143667 * 2 ^ 59
def prefixEnd_8143667 : Nat := 4983230072969 + 3 ^ 40 * 8143667 * 2
def baseEnd_8143667 : Nat := 4181615461158294599110463

theorem tailTrace_8143667 : CollatzResearch.WordTrace tailWord_8143667 prefixEnd_8143667 4181615461158294599110463 := by
  unfold tailWord_8143667
  simp only [CollatzResearch.WordTrace]
  refine ⟨297023936987892761439269255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198015957991928507626179503 297023936987892761439269255)
  ·
    refine ⟨445535905481839142158903883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297023936987892761439269255 445535905481839142158903883)
    ·
      refine ⟨668303858222758713238355825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445535905481839142158903883 668303858222758713238355825)
      ·
        refine ⟨501227893667069034928766869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668303858222758713238355825 501227893667069034928766869)
        ·
          refine ⟨23495057515643861012285947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501227893667069034928766869 23495057515643861012285947)
          ·
            refine ⟨35242586273465791518428921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23495057515643861012285947 35242586273465791518428921)
            ·
              refine ⟨26431939705099343638821691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35242586273465791518428921 26431939705099343638821691)
              ·
                refine ⟨39647909557649015458232537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26431939705099343638821691 39647909557649015458232537)
                ·
                  refine ⟨29735932168236761593674403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39647909557649015458232537 29735932168236761593674403)
                  ·
                    refine ⟨44603898252355142390511605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29735932168236761593674403 44603898252355142390511605)
                    ·
                      refine ⟨4181615461158294599110463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44603898252355142390511605 4181615461158294599110463)
                      ·
                        rfl

theorem cell23_8143667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_8143667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143667 prefixEnd_8143667 := by exact prefixLift 8143667
  have htrace : WordTrace (prefixWord ++ tailWord_8143667) baseStart_8143667 baseEnd_8143667 := by
    simpa [prefixWord, tailWord_8143667, baseEnd_8143667] using wordTrace_append hprefix tailTrace_8143667
  have hstable : (prefixWord ++ tailWord_8143667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143667).length < 2 ^ (prefixWord ++ tailWord_8143667).sum := by decide
  have hdescent : baseEnd_8143667 < baseStart_8143667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143680 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_8143680 : Nat := 118140960795 + 8143680 * 2 ^ 59
def prefixEnd_8143680 : Nat := 4983230072969 + 3 ^ 40 * 8143680 * 2
def baseEnd_8143680 : Nat := 4181622136406803048247903

theorem tailTrace_8143680 : CollatzResearch.WordTrace tailWord_8143680 prefixEnd_8143680 4181622136406803048247903 := by
  unfold tailWord_8143680
  simp only [CollatzResearch.WordTrace]
  refine ⟨148512205568422832329746247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198016274091230443106328329 148512205568422832329746247)
  ·
    refine ⟨222768308352634248494619371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148512205568422832329746247 222768308352634248494619371)
    ·
      refine ⟨334152462528951372741929057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222768308352634248494619371 334152462528951372741929057)
      ·
        refine ⟨250614346896713529556446793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334152462528951372741929057 250614346896713529556446793)
        ·
          refine ⟨187960760172535147167335095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250614346896713529556446793 187960760172535147167335095)
          ·
            refine ⟨281941140258802720751002643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187960760172535147167335095 281941140258802720751002643)
            ·
              refine ⟨422911710388204081126503965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281941140258802720751002643 422911710388204081126503965)
              ·
                refine ⟨158591891395576530422438987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422911710388204081126503965 158591891395576530422438987)
                ·
                  refine ⟨237887837093364795633658481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158591891395576530422438987 237887837093364795633658481)
                  ·
                    refine ⟨178415877820023596725243861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237887837093364795633658481 178415877820023596725243861)
                    ·
                      refine ⟨4181622136406803048247903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178415877820023596725243861 4181622136406803048247903)
                      ·
                        rfl

theorem cell23_8143680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_8143680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143680 prefixEnd_8143680 := by exact prefixLift 8143680
  have htrace : WordTrace (prefixWord ++ tailWord_8143680) baseStart_8143680 baseEnd_8143680 := by
    simpa [prefixWord, tailWord_8143680, baseEnd_8143680] using wordTrace_append hprefix tailTrace_8143680
  have hstable : (prefixWord ++ tailWord_8143680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143680).length < 2 ^ (prefixWord ++ tailWord_8143680).sum := by decide
  have hdescent : baseEnd_8143680 < baseStart_8143680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143754 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_8143754 : Nat := 118140960795 + 8143754 * 2 ^ 59
def prefixEnd_8143754 : Nat := 4983230072969 + 3 ^ 40 * 8143754 * 2
def baseEnd_8143754 : Nat := 4181660133975235758722563

theorem tailTrace_8143754 : CollatzResearch.WordTrace tailWord_8143754 prefixEnd_8143754 4181660133975235758722563 := by
  unfold tailWord_8143754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74256777534644393824421579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198018073425718383531790877 74256777534644393824421579)
  ·
    refine ⟨111385166301966590736632369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74256777534644393824421579 111385166301966590736632369)
    ·
      refine ⟨83538874726474943052474277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111385166301966590736632369 83538874726474943052474277)
      ·
        refine ⟨15663539011214051822338927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83538874726474943052474277 15663539011214051822338927)
        ·
          refine ⟨23495308516821077733508391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663539011214051822338927 23495308516821077733508391)
          ·
            refine ⟨35242962775231616600262587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23495308516821077733508391 35242962775231616600262587)
            ·
              refine ⟨52864444162847424900393881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35242962775231616600262587 52864444162847424900393881)
              ·
                refine ⟨39648333122135568675295411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52864444162847424900393881 39648333122135568675295411)
                ·
                  refine ⟨59472499683203353012943117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39648333122135568675295411 59472499683203353012943117)
                  ·
                    refine ⟨22302187381201257379853669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59472499683203353012943117 22302187381201257379853669)
                    ·
                      refine ⟨4181660133975235758722563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22302187381201257379853669 4181660133975235758722563)
                      ·
                        rfl

theorem cell23_8143754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_8143754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143754 prefixEnd_8143754 := by exact prefixLift 8143754
  have htrace : WordTrace (prefixWord ++ tailWord_8143754) baseStart_8143754 baseEnd_8143754 := by
    simpa [prefixWord, tailWord_8143754, baseEnd_8143754] using wordTrace_append hprefix tailTrace_8143754
  have hstable : (prefixWord ++ tailWord_8143754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143754).length < 2 ^ (prefixWord ++ tailWord_8143754).sum := by decide
  have hdescent : baseEnd_8143754 < baseStart_8143754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143767 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_8143767 : Nat := 118140960795 + 8143767 * 2 ^ 59
def prefixEnd_8143767 : Nat := 4983230072969 + 3 ^ 40 * 8143767 * 2
def baseEnd_8143767 : Nat := 4181666809223744207860003

theorem tailTrace_8143767 : CollatzResearch.WordTrace tailWord_8143767 prefixEnd_8143767 4181666809223744207860003 := by
  unfold tailWord_8143767
  simp only [CollatzResearch.WordTrace]
  refine ⟨297027584287530478517909555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198018389525020319011939703 297027584287530478517909555)
  ·
    refine ⟨445541376431295717776864333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297027584287530478517909555 445541376431295717776864333)
    ·
      refine ⟨167078016161735894166324125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445541376431295717776864333 167078016161735894166324125)
      ·
        refine ⟨62654256060650960312371547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167078016161735894166324125 62654256060650960312371547)
        ·
          refine ⟨93981384090976440468557321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62654256060650960312371547 93981384090976440468557321)
          ·
            refine ⟨70486038068232330351417991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93981384090976440468557321 70486038068232330351417991)
            ·
              refine ⟨105729057102348495527126987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70486038068232330351417991 105729057102348495527126987)
              ·
                refine ⟨158593585653522743290690481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105729057102348495527126987 158593585653522743290690481)
                ·
                  refine ⟨118945189240142057468017861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158593585653522743290690481 118945189240142057468017861)
                  ·
                    refine ⟨22302222982526635775253349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118945189240142057468017861 22302222982526635775253349)
                    ·
                      refine ⟨4181666809223744207860003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22302222982526635775253349 4181666809223744207860003)
                      ·
                        rfl

theorem cell23_8143767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_8143767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143767 prefixEnd_8143767 := by exact prefixLift 8143767
  have htrace : WordTrace (prefixWord ++ tailWord_8143767) baseStart_8143767 baseEnd_8143767 := by
    simpa [prefixWord, tailWord_8143767, baseEnd_8143767] using wordTrace_append hprefix tailTrace_8143767
  have hstable : (prefixWord ++ tailWord_8143767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143767).length < 2 ^ (prefixWord ++ tailWord_8143767).sum := by decide
  have hdescent : baseEnd_8143767 < baseStart_8143767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143787 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 3]
def baseStart_8143787 : Nat := 118140960795 + 8143787 * 2 ^ 59
def prefixEnd_8143787 : Nat := 4983230072969 + 3 ^ 40 * 8143787 * 2
def baseEnd_8143787 : Nat := 4181677078836834129609911

theorem tailTrace_8143787 : CollatzResearch.WordTrace tailWord_8143787 prefixEnd_8143787 4181677078836834129609911 := by
  unfold tailWord_8143787
  simp only [CollatzResearch.WordTrace]
  refine ⟨297028313747458021933637615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198018875831638681289091743 297028313747458021933637615)
  ·
    refine ⟨445542470621187032900456423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297028313747458021933637615 445542470621187032900456423)
    ·
      refine ⟨668313705931780549350684635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445542470621187032900456423 668313705931780549350684635)
      ·
        refine ⟨1002470558897670824026026953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668313705931780549350684635 1002470558897670824026026953)
        ·
          refine ⟨751852919173253118019520215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1002470558897670824026026953 751852919173253118019520215)
          ·
            refine ⟨1127779378759879677029280323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751852919173253118019520215 1127779378759879677029280323)
            ·
              refine ⟨1691669068139819515543920485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127779378759879677029280323 1691669068139819515543920485)
              ·
                refine ⟨317187950276216159164485091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1691669068139819515543920485 317187950276216159164485091)
                ·
                  refine ⟨475781925414324238746727637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317187950276216159164485091 475781925414324238746727637)
                  ·
                    refine ⟨11151138876898224345626429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 475781925414324238746727637 11151138876898224345626429)
                    ·
                      refine ⟨4181677078836834129609911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11151138876898224345626429 4181677078836834129609911)
                      ·
                        rfl

theorem cell23_8143787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 3].length) (baseStart_8143787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143787 prefixEnd_8143787 := by exact prefixLift 8143787
  have htrace : WordTrace (prefixWord ++ tailWord_8143787) baseStart_8143787 baseEnd_8143787 := by
    simpa [prefixWord, tailWord_8143787, baseEnd_8143787] using wordTrace_append hprefix tailTrace_8143787
  have hstable : (prefixWord ++ tailWord_8143787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143787).length < 2 ^ (prefixWord ++ tailWord_8143787).sum := by decide
  have hdescent : baseEnd_8143787 < baseStart_8143787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143855 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 1, 1, 3]
def baseStart_8143855 : Nat := 118140960795 + 8143855 * 2 ^ 59
def prefixEnd_8143855 : Nat := 4983230072969 + 3 ^ 40 * 8143855 * 2
def baseEnd_8143855 : Nat := 4181711995521339863559599

theorem tailTrace_8143855 : CollatzResearch.WordTrace tailWord_8143855 prefixEnd_8143855 4181711995521339863559599 := by
  unfold tailWord_8143855
  simp only [CollatzResearch.WordTrace]
  refine ⟨297030793911211669547113019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198020529274141113031408679 297030793911211669547113019)
  ·
    refine ⟨445546190866817504320669529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297030793911211669547113019 445546190866817504320669529)
    ·
      refine ⟨334159643150113128240502147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445546190866817504320669529 334159643150113128240502147)
      ·
        refine ⟨501239464725169692360753221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334159643150113128240502147 501239464725169692360753221)
        ·
          refine ⟨93982399635969317317641229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501239464725169692360753221 93982399635969317317641229)
          ·
            refine ⟨35243399863488493994115461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93982399635969317317641229 35243399863488493994115461)
            ·
              refine ⟨6608137474404092623896649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35243399863488493994115461 6608137474404092623896649)
              ·
                refine ⟨4956103105803069467922487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6608137474404092623896649 4956103105803069467922487)
                ·
                  refine ⟨7434154658704604201883731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956103105803069467922487 7434154658704604201883731)
                  ·
                    refine ⟨11151231988056906302825597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7434154658704604201883731 11151231988056906302825597)
                    ·
                      refine ⟨4181711995521339863559599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11151231988056906302825597 4181711995521339863559599)
                      ·
                        rfl

theorem cell23_8143855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 1, 3].length) (baseStart_8143855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143855 prefixEnd_8143855 := by exact prefixLift 8143855
  have htrace : WordTrace (prefixWord ++ tailWord_8143855) baseStart_8143855 baseEnd_8143855 := by
    simpa [prefixWord, tailWord_8143855, baseEnd_8143855] using wordTrace_append hprefix tailTrace_8143855
  have hstable : (prefixWord ++ tailWord_8143855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143855).length < 2 ^ (prefixWord ++ tailWord_8143855).sum := by decide
  have hdescent : baseEnd_8143855 < baseStart_8143855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143887 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_8143887 : Nat := 118140960795 + 8143887 * 2 ^ 59
def prefixEnd_8143887 : Nat := 4983230072969 + 3 ^ 40 * 8143887 * 2
def baseEnd_8143887 : Nat := 4181728426902283738359451

theorem tailTrace_8143887 : CollatzResearch.WordTrace tailWord_8143887 prefixEnd_8143887 4181728426902283738359451 := by
  unfold tailWord_8143887
  simp only [CollatzResearch.WordTrace]
  refine ⟨297031961047095739012277915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198021307364730492674851943 297031961047095739012277915)
  ·
    refine ⟨445547941570643608518416873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297031961047095739012277915 445547941570643608518416873)
    ·
      refine ⟨334160956177982706388812655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445547941570643608518416873 334160956177982706388812655)
      ·
        refine ⟨501241434266974059583218983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334160956177982706388812655 501241434266974059583218983)
        ·
          refine ⟨751862151400461089374828475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501241434266974059583218983 751862151400461089374828475)
          ·
            refine ⟨1127793227100691634062242713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751862151400461089374828475 1127793227100691634062242713)
            ·
              refine ⟨845844920325518725546682035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127793227100691634062242713 845844920325518725546682035)
              ·
                refine ⟨1268767380488278088320023053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845844920325518725546682035 1268767380488278088320023053)
                ·
                  refine ⟨475787767683104283120008645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268767380488278088320023053 475787767683104283120008645)
                  ·
                    refine ⟨89210206440582053085001621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475787767683104283120008645 89210206440582053085001621)
                    ·
                      refine ⟨4181728426902283738359451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89210206440582053085001621 4181728426902283738359451)
                      ·
                        rfl

theorem cell23_8143887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_8143887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143887 prefixEnd_8143887 := by exact prefixLift 8143887
  have htrace : WordTrace (prefixWord ++ tailWord_8143887) baseStart_8143887 baseEnd_8143887 := by
    simpa [prefixWord, tailWord_8143887, baseEnd_8143887] using wordTrace_append hprefix tailTrace_8143887
  have hstable : (prefixWord ++ tailWord_8143887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143887).length < 2 ^ (prefixWord ++ tailWord_8143887).sum := by decide
  have hdescent : baseEnd_8143887 < baseStart_8143887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143895 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 1, 1, 4]
def baseStart_8143895 : Nat := 118140960795 + 8143895 * 2 ^ 59
def prefixEnd_8143895 : Nat := 4983230072969 + 3 ^ 40 * 8143895 * 2
def baseEnd_8143895 : Nat := 4181732534747519707059415

theorem tailTrace_8143895 : CollatzResearch.WordTrace tailWord_8143895 prefixEnd_8143895 4181732534747519707059415 := by
  unfold tailWord_8143895
  simp only [CollatzResearch.WordTrace]
  refine ⟨297032252831066756378569139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198021501887377837585712759 297032252831066756378569139)
  ·
    refine ⟨445548379246600134567853709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297032252831066756378569139 445548379246600134567853709)
    ·
      refine ⟨167080642217475050462945141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445548379246600134567853709 167080642217475050462945141)
      ·
        refine ⟨15663810207888285980901107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167080642217475050462945141 15663810207888285980901107)
        ·
          refine ⟨23495715311832428971351661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663810207888285980901107 23495715311832428971351661)
          ·
            refine ⟨8810893241937160864256873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23495715311832428971351661 8810893241937160864256873)
            ·
              refine ⟨6608169931452870648192655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8810893241937160864256873 6608169931452870648192655)
              ·
                refine ⟨9912254897179305972288983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608169931452870648192655 9912254897179305972288983)
                ·
                  refine ⟨14868382345768958958433475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912254897179305972288983 14868382345768958958433475)
                  ·
                    refine ⟨22302573518653438437650213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14868382345768958958433475 22302573518653438437650213)
                    ·
                      refine ⟨4181732534747519707059415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22302573518653438437650213 4181732534747519707059415)
                      ·
                        rfl

theorem cell23_8143895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_8143895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143895 prefixEnd_8143895 := by exact prefixLift 8143895
  have htrace : WordTrace (prefixWord ++ tailWord_8143895) baseStart_8143895 baseEnd_8143895 := by
    simpa [prefixWord, tailWord_8143895, baseEnd_8143895] using wordTrace_append hprefix tailTrace_8143895
  have hstable : (prefixWord ++ tailWord_8143895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143895).length < 2 ^ (prefixWord ++ tailWord_8143895).sum := by decide
  have hdescent : baseEnd_8143895 < baseStart_8143895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143928 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_8143928 : Nat := 118140960795 + 8143928 * 2 ^ 59
def prefixEnd_8143928 : Nat := 4983230072969 + 3 ^ 40 * 8143928 * 2
def baseEnd_8143928 : Nat := 4181749479609118077946763

theorem tailTrace_8143928 : CollatzResearch.WordTrace tailWord_8143928 prefixEnd_8143928 4181749479609118077946763 := by
  unfold tailWord_8143928
  simp only [CollatzResearch.WordTrace]
  refine ⟨148516728219973601507260219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198022304293298135343013625 148516728219973601507260219)
  ·
    refine ⟨222775092329960402260890329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148516728219973601507260219 222775092329960402260890329)
    ·
      refine ⟨167081319247470301695667747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222775092329960402260890329 167081319247470301695667747)
      ·
        refine ⟨250621978871205452543501621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167081319247470301695667747 250621978871205452543501621)
        ·
          refine ⟨23495810519175511175953277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250621978871205452543501621 23495810519175511175953277)
          ·
            refine ⟨8810928944690816690982479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23495810519175511175953277 8810928944690816690982479)
            ·
              refine ⟨13216393417036225036473719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810928944690816690982479 13216393417036225036473719)
              ·
                refine ⟨19824590125554337554710579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13216393417036225036473719 19824590125554337554710579)
                ·
                  refine ⟨29736885188331506332065869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19824590125554337554710579 29736885188331506332065869)
                  ·
                    refine ⟨11151331945624314874524701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29736885188331506332065869 11151331945624314874524701)
                    ·
                      refine ⟨4181749479609118077946763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11151331945624314874524701 4181749479609118077946763)
                      ·
                        rfl

theorem cell23_8143928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_8143928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143928 prefixEnd_8143928 := by exact prefixLift 8143928
  have htrace : WordTrace (prefixWord ++ tailWord_8143928) baseStart_8143928 baseEnd_8143928 := by
    simpa [prefixWord, tailWord_8143928, baseEnd_8143928] using wordTrace_append hprefix tailTrace_8143928
  have hstable : (prefixWord ++ tailWord_8143928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143928).length < 2 ^ (prefixWord ++ tailWord_8143928).sum := by decide
  have hdescent : baseEnd_8143928 < baseStart_8143928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143968 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 4, 2, 2]
def baseStart_8143968 : Nat := 118140960795 + 8143968 * 2 ^ 59
def prefixEnd_8143968 : Nat := 4983230072969 + 3 ^ 40 * 8143968 * 2
def baseEnd_8143968 : Nat := 4181770018835297921446579

theorem tailTrace_8143968 : CollatzResearch.WordTrace tailWord_8143968 prefixEnd_8143968 4181770018835297921446579 := by
  unfold tailWord_8143968
  simp only [CollatzResearch.WordTrace]
  refine ⟨148517457679901144922988279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198023276906534859897317705 148517457679901144922988279)
  ·
    refine ⟨222776186519851717384482419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148517457679901144922988279 222776186519851717384482419)
    ·
      refine ⟨334164279779777576076723629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222776186519851717384482419 334164279779777576076723629)
      ·
        refine ⟨125311604917416591028771361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334164279779777576076723629 125311604917416591028771361)
        ·
          refine ⟨93983703688062443271578521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125311604917416591028771361 93983703688062443271578521)
          ·
            refine ⟨70487777766046832453683891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93983703688062443271578521 70487777766046832453683891)
            ·
              refine ⟨105731666649070248680525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70487777766046832453683891 105731666649070248680525837)
              ·
                refine ⟨39649374993401343255197189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105731666649070248680525837 39649374993401343255197189)
                ·
                  refine ⟨7434257811262751860349473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39649374993401343255197189 7434257811262751860349473)
                  ·
                    refine ⟨5575693358447063895262105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7434257811262751860349473 5575693358447063895262105)
                    ·
                      refine ⟨4181770018835297921446579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575693358447063895262105 4181770018835297921446579)
                      ·
                        rfl

theorem cell23_8143968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_8143968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143968 prefixEnd_8143968 := by exact prefixLift 8143968
  have htrace : WordTrace (prefixWord ++ tailWord_8143968) baseStart_8143968 baseEnd_8143968 := by
    simpa [prefixWord, tailWord_8143968, baseEnd_8143968] using wordTrace_append hprefix tailTrace_8143968
  have hstable : (prefixWord ++ tailWord_8143968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143968).length < 2 ^ (prefixWord ++ tailWord_8143968).sum := by decide
  have hdescent : baseEnd_8143968 < baseStart_8143968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8143989 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8143989 : Nat := 118140960795 + 8143989 * 2 ^ 59
def prefixEnd_8143989 : Nat := 4983230072969 + 3 ^ 40 * 8143989 * 2
def baseEnd_8143989 : Nat := 4181780801929042339283983

theorem tailTrace_8143989 : CollatzResearch.WordTrace tailWord_8143989 prefixEnd_8143989 4181780801929042339283983 := by
  unfold tailWord_8143989
  simp only [CollatzResearch.WordTrace]
  refine ⟨297035681292726210432491021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198023787528484140288327347 297035681292726210432491021)
  ·
    refine ⟨111388380484772328912184133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297035681292726210432491021 111388380484772328912184133)
    ·
      refine ⟨20885321340894811671034525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111388380484772328912184133 20885321340894811671034525)
      ·
        refine ⟨7831995502835554376637947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20885321340894811671034525 7831995502835554376637947)
        ·
          refine ⟨11747993254253331564956921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7831995502835554376637947 11747993254253331564956921)
          ·
            refine ⟨8810994940689998673717691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11747993254253331564956921 8810994940689998673717691)
            ·
              refine ⟨13216492411034998010576537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810994940689998673717691 13216492411034998010576537)
              ·
                refine ⟨9912369308276248507932403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13216492411034998010576537 9912369308276248507932403)
                ·
                  refine ⟨14868553962414372761898605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912369308276248507932403 14868553962414372761898605)
                  ·
                    refine ⟨5575707735905389785711977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14868553962414372761898605 5575707735905389785711977)
                    ·
                      refine ⟨4181780801929042339283983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575707735905389785711977 4181780801929042339283983)
                      ·
                        rfl

theorem cell23_8143989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8143989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8143989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8143989 prefixEnd_8143989 := by exact prefixLift 8143989
  have htrace : WordTrace (prefixWord ++ tailWord_8143989) baseStart_8143989 baseEnd_8143989 := by
    simpa [prefixWord, tailWord_8143989, baseEnd_8143989] using wordTrace_append hprefix tailTrace_8143989
  have hstable : (prefixWord ++ tailWord_8143989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8143989).length < 2 ^ (prefixWord ++ tailWord_8143989).sum := by decide
  have hdescent : baseEnd_8143989 < baseStart_8143989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8143989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144011 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 4, 5, 2]
def baseStart_8144011 : Nat := 118140960795 + 8144011 * 2 ^ 59
def prefixEnd_8144011 : Nat := 4983230072969 + 3 ^ 40 * 8144011 * 2
def baseEnd_8144011 : Nat := 4181792098503441253208881

theorem tailTrace_8144011 : CollatzResearch.WordTrace tailWord_8144011 prefixEnd_8144011 4181792098503441253208881 := by
  unfold tailWord_8144011
  simp only [CollatzResearch.WordTrace]
  refine ⟨297036483698646508189791887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198024322465764338793194591 297036483698646508189791887)
  ·
    refine ⟨445554725547969762284687831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297036483698646508189791887 445554725547969762284687831)
    ·
      refine ⟨668332088321954643427031747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445554725547969762284687831 668332088321954643427031747)
      ·
        refine ⟨1002498132482931965140547621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668332088321954643427031747 1002498132482931965140547621)
        ·
          refine ⟨187968399840549743463852679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1002498132482931965140547621 187968399840549743463852679)
          ·
            refine ⟨281952599760824615195779019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187968399840549743463852679 281952599760824615195779019)
            ·
              refine ⟨422928899641236922793668529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281952599760824615195779019 422928899641236922793668529)
              ·
                refine ⟨317196674730927692095251397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422928899641236922793668529 317196674730927692095251397)
                ·
                  refine ⟨59474376512048942267859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317196674730927692095251397 59474376512048942267859637)
                  ·
                    refine ⟨5575722798004588337611841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59474376512048942267859637 5575722798004588337611841)
                    ·
                      refine ⟨4181792098503441253208881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575722798004588337611841 4181792098503441253208881)
                      ·
                        rfl

theorem cell23_8144011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5, 2].length) (baseStart_8144011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144011 prefixEnd_8144011 := by exact prefixLift 8144011
  have htrace : WordTrace (prefixWord ++ tailWord_8144011) baseStart_8144011 baseEnd_8144011 := by
    simpa [prefixWord, tailWord_8144011, baseEnd_8144011] using wordTrace_append hprefix tailTrace_8144011
  have hstable : (prefixWord ++ tailWord_8144011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144011).length < 2 ^ (prefixWord ++ tailWord_8144011).sum := by decide
  have hdescent : baseEnd_8144011 < baseStart_8144011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144028 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_8144028 : Nat := 118140960795 + 8144028 * 2 ^ 59
def prefixEnd_8144028 : Nat := 4983230072969 + 3 ^ 40 * 8144028 * 2
def baseEnd_8144028 : Nat := 4181800827674567686696303

theorem tailTrace_8144028 : CollatzResearch.WordTrace tailWord_8144028 prefixEnd_8144028 4181800827674567686696303 := by
  unfold tailWord_8144028
  simp only [CollatzResearch.WordTrace]
  refine ⟨148518551869792460046580369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198024735826389946728773825 148518551869792460046580369)
  ·
    refine ⟨111388913902344345034935277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148518551869792460046580369 111388913902344345034935277)
    ·
      refine ⟨41770842713379129388100729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111388913902344345034935277 41770842713379129388100729)
      ·
        refine ⟨31328132035034347041075547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41770842713379129388100729 31328132035034347041075547)
        ·
          refine ⟨46992198052551520561613321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31328132035034347041075547 46992198052551520561613321)
          ·
            refine ⟨35244148539413640421209991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46992198052551520561613321 35244148539413640421209991)
            ·
              refine ⟨52866222809120460631814987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35244148539413640421209991 52866222809120460631814987)
              ·
                refine ⟨79299334213680690947722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52866222809120460631814987 79299334213680690947722481)
                ·
                  refine ⟨59474500660260518210791861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79299334213680690947722481 59474500660260518210791861)
                  ·
                    refine ⟨5575734436899423582261737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59474500660260518210791861 5575734436899423582261737)
                    ·
                      refine ⟨4181800827674567686696303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575734436899423582261737 4181800827674567686696303)
                      ·
                        rfl

theorem cell23_8144028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_8144028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144028 prefixEnd_8144028 := by exact prefixLift 8144028
  have htrace : WordTrace (prefixWord ++ tailWord_8144028) baseStart_8144028 baseEnd_8144028 := by
    simpa [prefixWord, tailWord_8144028, baseEnd_8144028] using wordTrace_append hprefix tailTrace_8144028
  have hstable : (prefixWord ++ tailWord_8144028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144028).length < 2 ^ (prefixWord ++ tailWord_8144028).sum := by decide
  have hdescent : baseEnd_8144028 < baseStart_8144028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144051 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 5, 4]
def baseStart_8144051 : Nat := 118140960795 + 8144051 * 2 ^ 59
def prefixEnd_8144051 : Nat := 4983230072969 + 3 ^ 40 * 8144051 * 2
def baseEnd_8144051 : Nat := 1393937545909873698902899

theorem tailTrace_8144051 : CollatzResearch.WordTrace tailWord_8144051 prefixEnd_8144051 1393937545909873698902899 := by
  unfold tailWord_8144051
  simp only [CollatzResearch.WordTrace]
  refine ⟨297037942618501595021248007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198025295079001063347498671 297037942618501595021248007)
  ·
    refine ⟨445556913927752392531872011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297037942618501595021248007 445556913927752392531872011)
    ·
      refine ⟨668335370891628588797808017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445556913927752392531872011 668335370891628588797808017)
      ·
        refine ⟨501251528168721441598356013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668335370891628588797808017 501251528168721441598356013)
        ·
          refine ⟨187969323063270540599383505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501251528168721441598356013 187969323063270540599383505)
          ·
            refine ⟨140976992297452905449537629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187969323063270540599383505 140976992297452905449537629)
            ·
              refine ⟨52866372111544839543576611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140976992297452905449537629 52866372111544839543576611)
              ·
                refine ⟨79299558167317259315364917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52866372111544839543576611 79299558167317259315364917)
                ·
                  refine ⟨7434333578185993060815461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79299558167317259315364917 7434333578185993060815461)
                  ·
                    refine ⟨1393937545909873698902899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7434333578185993060815461 1393937545909873698902899)
                    ·
                      rfl

theorem cell23_8144051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 4].length) (baseStart_8144051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144051 prefixEnd_8144051 := by exact prefixLift 8144051
  have htrace : WordTrace (prefixWord ++ tailWord_8144051) baseStart_8144051 baseEnd_8144051 := by
    simpa [prefixWord, tailWord_8144051, baseEnd_8144051] using wordTrace_append hprefix tailTrace_8144051
  have hstable : (prefixWord ++ tailWord_8144051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144051).length < 2 ^ (prefixWord ++ tailWord_8144051).sum := by decide
  have hdescent : baseEnd_8144051 < baseStart_8144051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
