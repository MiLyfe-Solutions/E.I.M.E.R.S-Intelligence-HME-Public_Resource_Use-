import V185TrunkScan23Chunk0438

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2595076 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_2595076 : Nat := 118140960795 + 2595076 * 2 ^ 59
def prefixEnd_2595076 : Nat := 4983230072969 + 3 ^ 40 * 2595076 * 2
def baseEnd_2595076 : Nat := 444173774315731328971823

theorem tailTrace_2595076 : CollatzResearch.WordTrace tailWord_2595076 prefixEnd_2595076 444173774315731328971823 := by
  unfold tailWord_2595076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47325098773245165270330541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63100131697660220360440721 47325098773245165270330541)
  ·
    refine ⟨17746912039966936976373953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47325098773245165270330541 17746912039966936976373953)
    ·
      refine ⟨13310184029975202732280465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17746912039966936976373953 13310184029975202732280465)
      ·
        refine ⟨9982638022481402049210349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13310184029975202732280465 9982638022481402049210349)
        ·
          refine ⟨3743489258430525768453881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9982638022481402049210349 3743489258430525768453881)
          ·
            refine ⟨2807616943822894326340411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743489258430525768453881 2807616943822894326340411)
            ·
              refine ⟨4211425415734341489510617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807616943822894326340411 4211425415734341489510617)
              ·
                refine ⟨3158569061800756117132963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211425415734341489510617 3158569061800756117132963)
                ·
                  refine ⟨4737853592701134175699445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158569061800756117132963 4737853592701134175699445)
                  ·
                    refine ⟨444173774315731328971823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4737853592701134175699445 444173774315731328971823)
                    ·
                      rfl

theorem cell23_2595076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_2595076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595076 prefixEnd_2595076 := by exact prefixLift 2595076
  have htrace : WordTrace (prefixWord ++ tailWord_2595076) baseStart_2595076 baseEnd_2595076 := by
    simpa [prefixWord, tailWord_2595076, baseEnd_2595076] using wordTrace_append hprefix tailTrace_2595076
  have hstable : (prefixWord ++ tailWord_2595076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595076).length < 2 ^ (prefixWord ++ tailWord_2595076).sum := by decide
  have hdescent : baseEnd_2595076 < baseStart_2595076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595106 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2595106 : Nat := 118140960795 + 2595106 * 2 ^ 59
def prefixEnd_2595106 : Nat := 4983230072969 + 3 ^ 40 * 2595106 * 2
def baseEnd_2595106 : Nat := 444178909122276289846777

theorem tailTrace_2595106 : CollatzResearch.WordTrace tailWord_2595106 prefixEnd_2595106 444178909122276289846777 := by
  unfold tailWord_2595106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662822934095411416063293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63100861157587763776168781 23662822934095411416063293)
  ·
    refine ⟨8873558600285779281023735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23662822934095411416063293 8873558600285779281023735)
    ·
      refine ⟨13310337900428668921535603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8873558600285779281023735 13310337900428668921535603)
      ·
        refine ⟨19965506850643003382303405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13310337900428668921535603 19965506850643003382303405)
        ·
          refine ⟨7487065068991126268363777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19965506850643003382303405 7487065068991126268363777)
          ·
            refine ⟨5615298801743344701272833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7487065068991126268363777 5615298801743344701272833)
            ·
              refine ⟨4211474101307508525954625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5615298801743344701272833 4211474101307508525954625)
              ·
                refine ⟨3158605575980631394465969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211474101307508525954625 3158605575980631394465969)
                ·
                  refine ⟨2368954181985473545849477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3158605575980631394465969 2368954181985473545849477)
                  ·
                    refine ⟨444178909122276289846777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368954181985473545849477 444178909122276289846777)
                    ·
                      rfl

theorem cell23_2595106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2595106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595106 prefixEnd_2595106 := by exact prefixLift 2595106
  have htrace : WordTrace (prefixWord ++ tailWord_2595106) baseStart_2595106 baseEnd_2595106 := by
    simpa [prefixWord, tailWord_2595106, baseEnd_2595106] using wordTrace_append hprefix tailTrace_2595106
  have hstable : (prefixWord ++ tailWord_2595106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595106).length < 2 ^ (prefixWord ++ tailWord_2595106).sum := by decide
  have hdescent : baseEnd_2595106 < baseStart_2595106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595129 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2595129 : Nat := 118140960795 + 2595129 * 2 ^ 59
def prefixEnd_2595129 : Nat := 4983230072969 + 3 ^ 40 * 2595129 * 2
def baseEnd_2595129 : Nat := 1332548537421882279552725

theorem tailTrace_2595129 : CollatzResearch.WordTrace tailWord_2595129 prefixEnd_2595129 1332548537421882279552725 := by
  unfold tailWord_2595129
  simp only [CollatzResearch.WordTrace]
  refine ⟨94652130615298320592340441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63101420410198880394893627 94652130615298320592340441)
  ·
    refine ⟨70989097961473740444255331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94652130615298320592340441 70989097961473740444255331)
    ·
      refine ⟨106483646942210610666382997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70989097961473740444255331 106483646942210610666382997)
      ·
        refine ⟨4991420950416122374986703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106483646942210610666382997 4991420950416122374986703)
        ·
          refine ⟨7487131425624183562480055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991420950416122374986703 7487131425624183562480055)
          ·
            refine ⟨11230697138436275343720083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7487131425624183562480055 11230697138436275343720083)
            ·
              refine ⟨16846045707654413015580125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11230697138436275343720083 16846045707654413015580125)
              ·
                refine ⟨6317267140370404880842547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16846045707654413015580125 6317267140370404880842547)
                ·
                  refine ⟨9475900710555607321263821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6317267140370404880842547 9475900710555607321263821)
                  ·
                    refine ⟨3553462766458352745473933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9475900710555607321263821 3553462766458352745473933)
                    ·
                      refine ⟨1332548537421882279552725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3553462766458352745473933 1332548537421882279552725)
                      ·
                        rfl

theorem cell23_2595129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2595129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595129 prefixEnd_2595129 := by exact prefixLift 2595129
  have htrace : WordTrace (prefixWord ++ tailWord_2595129) baseStart_2595129 baseEnd_2595129 := by
    simpa [prefixWord, tailWord_2595129, baseEnd_2595129] using wordTrace_append hprefix tailTrace_2595129
  have hstable : (prefixWord ++ tailWord_2595129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595129).length < 2 ^ (prefixWord ++ tailWord_2595129).sum := by decide
  have hdescent : baseEnd_2595129 < baseStart_2595129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595139 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 3, 3, 2]
def baseStart_2595139 : Nat := 118140960795 + 2595139 * 2 ^ 59
def prefixEnd_2595139 : Nat := 4983230072969 + 3 ^ 40 * 2595139 * 2
def baseEnd_2595139 : Nat := 1332553672228427240427679

theorem tailTrace_2595139 : CollatzResearch.WordTrace tailWord_2595139 prefixEnd_2595139 1332553672228427240427679 := by
  unfold tailWord_2595139
  simp only [CollatzResearch.WordTrace]
  refine ⟨94652495345262092300204471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63101663563508061533469647 94652495345262092300204471)
  ·
    refine ⟨141978743017893138450306707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94652495345262092300204471 141978743017893138450306707)
    ·
      refine ⟨212968114526839707675460061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141978743017893138450306707 212968114526839707675460061)
      ·
        refine ⟨79863042947564890378297523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212968114526839707675460061 79863042947564890378297523)
        ·
          refine ⟨119794564421347335567446285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79863042947564890378297523 119794564421347335567446285)
          ·
            refine ⟨44922961658005250837792357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119794564421347335567446285 44922961658005250837792357)
            ·
              refine ⟨8423055310875984532086067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44922961658005250837792357 8423055310875984532086067)
              ·
                refine ⟨12634582966313976798129101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8423055310875984532086067 12634582966313976798129101)
                ·
                  refine ⟨4737968612367741299298413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12634582966313976798129101 4737968612367741299298413)
                  ·
                    refine ⟨1776738229637902987236905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4737968612367741299298413 1776738229637902987236905)
                    ·
                      refine ⟨1332553672228427240427679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776738229637902987236905 1332553672228427240427679)
                      ·
                        rfl

theorem cell23_2595139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_2595139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595139 prefixEnd_2595139 := by exact prefixLift 2595139
  have htrace : WordTrace (prefixWord ++ tailWord_2595139) baseStart_2595139 baseEnd_2595139 := by
    simpa [prefixWord, tailWord_2595139, baseEnd_2595139] using wordTrace_append hprefix tailTrace_2595139
  have hstable : (prefixWord ++ tailWord_2595139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595139).length < 2 ^ (prefixWord ++ tailWord_2595139).sum := by decide
  have hdescent : baseEnd_2595139 < baseStart_2595139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595145 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_2595145 : Nat := 118140960795 + 2595145 * 2 ^ 59
def prefixEnd_2595145 : Nat := 4983230072969 + 3 ^ 40 * 2595145 * 2
def baseEnd_2595145 : Nat := 444185584370784738984217

theorem tailTrace_2595145 : CollatzResearch.WordTrace tailWord_2595145 prefixEnd_2595145 444185584370784738984217 := by
  unfold tailWord_2595145
  simp only [CollatzResearch.WordTrace]
  refine ⟨94652714183240355324922889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63101809455493570216615259 94652714183240355324922889)
  ·
    refine ⟨70989535637430266493692167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94652714183240355324922889 70989535637430266493692167)
    ·
      refine ⟨106484303456145399740538251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70989535637430266493692167 106484303456145399740538251)
      ·
        refine ⟨159726455184218099610807377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106484303456145399740538251 159726455184218099610807377)
        ·
          refine ⟨119794841388163574708105533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159726455184218099610807377 119794841388163574708105533)
          ·
            refine ⟨44923065520561340515539575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119794841388163574708105533 44923065520561340515539575)
            ·
              refine ⟨67384598280842010773309363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44923065520561340515539575 67384598280842010773309363)
              ·
                refine ⟨101076897421263016159964045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67384598280842010773309363 101076897421263016159964045)
                ·
                  refine ⟨37903836532973631059986517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101076897421263016159964045 37903836532973631059986517)
                  ·
                    refine ⟨444185584370784738984217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37903836532973631059986517 444185584370784738984217)
                    ·
                      rfl

theorem cell23_2595145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_2595145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595145 prefixEnd_2595145 := by exact prefixLift 2595145
  have htrace : WordTrace (prefixWord ++ tailWord_2595145) baseStart_2595145 baseEnd_2595145 := by
    simpa [prefixWord, tailWord_2595145, baseEnd_2595145] using wordTrace_append hprefix tailTrace_2595145
  have hstable : (prefixWord ++ tailWord_2595145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595145).length < 2 ^ (prefixWord ++ tailWord_2595145).sum := by decide
  have hdescent : baseEnd_2595145 < baseStart_2595145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595186 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_2595186 : Nat := 118140960795 + 2595186 * 2 ^ 59
def prefixEnd_2595186 : Nat := 4983230072969 + 3 ^ 40 * 2595186 * 2
def baseEnd_2595186 : Nat := 1332577805819188556539963

theorem tailTrace_2595186 : CollatzResearch.WordTrace tailWord_2595186 prefixEnd_2595186 1332577805819188556539963 := by
  unfold tailWord_2595186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23663552394022954831791353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63102806384061212884776941 23663552394022954831791353)
  ·
    refine ⟨17747664295517216123843515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23663552394022954831791353 17747664295517216123843515)
    ·
      refine ⟨26621496443275824185765273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17747664295517216123843515 26621496443275824185765273)
      ·
        refine ⟨19966122332456868139323955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26621496443275824185765273 19966122332456868139323955)
        ·
          refine ⟨29949183498685302208985933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19966122332456868139323955 29949183498685302208985933)
          ·
            refine ⟨11230943812006988328369725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29949183498685302208985933 11230943812006988328369725)
            ·
              refine ⟨4211603929502620623138647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11230943812006988328369725 4211603929502620623138647)
              ·
                refine ⟨6317405894253930934707971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211603929502620623138647 6317405894253930934707971)
                ·
                  refine ⟨9476108841380896402061957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6317405894253930934707971 9476108841380896402061957)
                  ·
                    refine ⟨1776770407758918075386617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9476108841380896402061957 1776770407758918075386617)
                    ·
                      refine ⟨1332577805819188556539963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776770407758918075386617 1332577805819188556539963)
                      ·
                        rfl

theorem cell23_2595186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_2595186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595186 prefixEnd_2595186 := by exact prefixLift 2595186
  have htrace : WordTrace (prefixWord ++ tailWord_2595186) baseStart_2595186 baseEnd_2595186 := by
    simpa [prefixWord, tailWord_2595186, baseEnd_2595186] using wordTrace_append hprefix tailTrace_2595186
  have hstable : (prefixWord ++ tailWord_2595186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595186).length < 2 ^ (prefixWord ++ tailWord_2595186).sum := by decide
  have hdescent : baseEnd_2595186 < baseStart_2595186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595232 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2595232 : Nat := 118140960795 + 2595232 * 2 ^ 59
def prefixEnd_2595232 : Nat := 4983230072969 + 3 ^ 40 * 2595232 * 2
def baseEnd_2595232 : Nat := 1332601425929295376564751

theorem tailTrace_2595232 : CollatzResearch.WordTrace tailWord_2595232 prefixEnd_2595232 1332601425929295376564751 := by
  unfold tailWord_2595232
  simp only [CollatzResearch.WordTrace]
  refine ⟨47327943666962584591669975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63103924889283446122226633 47327943666962584591669975)
  ·
    refine ⟨70991915500443876887504963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47327943666962584591669975 70991915500443876887504963)
    ·
      refine ⟨106487873250665815331257445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70991915500443876887504963 106487873250665815331257445)
      ·
        refine ⟨19966476234499840374610771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106487873250665815331257445 19966476234499840374610771)
        ·
          refine ⟨29949714351749760561916157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19966476234499840374610771 29949714351749760561916157)
          ·
            refine ⟨11231142881906160210718559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29949714351749760561916157 11231142881906160210718559)
            ·
              refine ⟨16846714322859240316077839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11231142881906160210718559 16846714322859240316077839)
              ·
                refine ⟨25270071484288860474116759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16846714322859240316077839 25270071484288860474116759)
                ·
                  refine ⟨37905107226433290711175139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25270071484288860474116759 37905107226433290711175139)
                  ·
                    refine ⟨56857660839649936066762709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37905107226433290711175139 56857660839649936066762709)
                    ·
                      refine ⟨1332601425929295376564751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56857660839649936066762709 1332601425929295376564751)
                      ·
                        rfl

theorem cell23_2595232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2595232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595232 prefixEnd_2595232 := by exact prefixLift 2595232
  have htrace : WordTrace (prefixWord ++ tailWord_2595232) baseStart_2595232 baseEnd_2595232 := by
    simpa [prefixWord, tailWord_2595232, baseEnd_2595232] using wordTrace_append hprefix tailTrace_2595232
  have hstable : (prefixWord ++ tailWord_2595232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595232).length < 2 ^ (prefixWord ++ tailWord_2595232).sum := by decide
  have hdescent : baseEnd_2595232 < baseStart_2595232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595336 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_2595336 : Nat := 118140960795 + 2595336 * 2 ^ 59
def prefixEnd_2595336 : Nat := 4983230072969 + 3 ^ 40 * 2595336 * 2
def baseEnd_2595336 : Nat := 1332654827917362969664273

theorem tailTrace_2595336 : CollatzResearch.WordTrace tailWord_2595336 prefixEnd_2595336 1332654827917362969664273 := by
  unfold tailWord_2595336
  simp only [CollatzResearch.WordTrace]
  refine ⟨47329840262774197472562931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63106453683698929963417241 47329840262774197472562931)
  ·
    refine ⟨70994760394161296208844397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47329840262774197472562931 70994760394161296208844397)
    ·
      refine ⟨26623035147810486078316649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70994760394161296208844397 26623035147810486078316649)
      ·
        refine ⟨19967276360857864558737487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26623035147810486078316649 19967276360857864558737487)
        ·
          refine ⟨29950914541286796838106231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19967276360857864558737487 29950914541286796838106231)
          ·
            refine ⟨44926371811930195257159347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29950914541286796838106231 44926371811930195257159347)
            ·
              refine ⟨67389557717895292885739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44926371811930195257159347 67389557717895292885739021)
              ·
                refine ⟨25271084144210734832152133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67389557717895292885739021 25271084144210734832152133)
                ·
                  refine ⟨4738328277039512781028525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25271084144210734832152133 4738328277039512781028525)
                  ·
                    refine ⟨1776873103889817292885697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4738328277039512781028525 1776873103889817292885697)
                    ·
                      refine ⟨1332654827917362969664273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776873103889817292885697 1332654827917362969664273)
                      ·
                        rfl

theorem cell23_2595336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_2595336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595336 prefixEnd_2595336 := by exact prefixLift 2595336
  have htrace : WordTrace (prefixWord ++ tailWord_2595336) baseStart_2595336 baseEnd_2595336 := by
    simpa [prefixWord, tailWord_2595336, baseEnd_2595336] using wordTrace_append hprefix tailTrace_2595336
  have hstable : (prefixWord ++ tailWord_2595336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595336).length < 2 ^ (prefixWord ++ tailWord_2595336).sum := by decide
  have hdescent : baseEnd_2595336 < baseStart_2595336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595379 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4]
def baseStart_2595379 : Nat := 118140960795 + 2595379 * 2 ^ 59
def prefixEnd_2595379 : Nat := 4983230072969 + 3 ^ 40 * 2595379 * 2
def baseEnd_2595379 : Nat := 1332676907585506301426575

theorem tailTrace_2595379 : CollatzResearch.WordTrace tailWord_2595379 prefixEnd_2595379 1332676907585506301426575 := by
  unfold tailWord_2595379
  simp only [CollatzResearch.WordTrace]
  refine ⟨94661248864392613288941191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63107499242928408859294127 94661248864392613288941191)
  ·
    refine ⟨141991873296588919933411787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94661248864392613288941191 141991873296588919933411787)
    ·
      refine ⟨212987809944883379900117681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141991873296588919933411787 212987809944883379900117681)
      ·
        refine ⟨159740857458662534925088261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212987809944883379900117681 159740857458662534925088261)
        ·
          refine ⟨29951410773499225298454049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159740857458662534925088261 29951410773499225298454049)
          ·
            refine ⟨22463558080124418973840537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29951410773499225298454049 22463558080124418973840537)
            ·
              refine ⟨16847668560093314230380403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22463558080124418973840537 16847668560093314230380403)
              ·
                refine ⟨25271502840139971345570605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16847668560093314230380403 25271502840139971345570605)
                ·
                  refine ⟨9476813565052489254588977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25271502840139971345570605 9476813565052489254588977)
                  ·
                    refine ⟨7107610173789366940941733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9476813565052489254588977 7107610173789366940941733)
                    ·
                      refine ⟨1332676907585506301426575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7107610173789366940941733 1332676907585506301426575)
                      ·
                        rfl

theorem cell23_2595379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_2595379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595379 prefixEnd_2595379 := by exact prefixLift 2595379
  have htrace : WordTrace (prefixWord ++ tailWord_2595379) baseStart_2595379 baseEnd_2595379 := by
    simpa [prefixWord, tailWord_2595379, baseEnd_2595379] using wordTrace_append hprefix tailTrace_2595379
  have hstable : (prefixWord ++ tailWord_2595379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595379).length < 2 ^ (prefixWord ++ tailWord_2595379).sum := by decide
  have hdescent : baseEnd_2595379 < baseStart_2595379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595386 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_2595386 : Nat := 118140960795 + 2595386 * 2 ^ 59
def prefixEnd_2595386 : Nat := 4983230072969 + 3 ^ 40 * 2595386 * 2
def baseEnd_2595386 : Nat := 1332680501950087774039043

theorem tailTrace_2595386 : CollatzResearch.WordTrace tailWord_2595386 prefixEnd_2595386 1332680501950087774039043 := by
  unfold tailWord_2595386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23665376043841813371111503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63107669450244835656297341 23665376043841813371111503)
  ·
    refine ⟨35498064065762720056667255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23665376043841813371111503 35498064065762720056667255)
    ·
      refine ⟨53247096098644080085000883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35498064065762720056667255 53247096098644080085000883)
      ·
        refine ⟨79870644147966120127501325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53247096098644080085000883 79870644147966120127501325)
        ·
          refine ⟨29951491555487295047812997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79870644147966120127501325 29951491555487295047812997)
          ·
            refine ⟨5615904666653867821464937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29951491555487295047812997 5615904666653867821464937)
            ·
              refine ⟨4211928499990400866098703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5615904666653867821464937 4211928499990400866098703)
              ·
                refine ⟨6317892749985601299148055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211928499990400866098703 6317892749985601299148055)
                ·
                  refine ⟨9476839124978401948722083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6317892749985601299148055 9476839124978401948722083)
                  ·
                    refine ⟨14215258687467602923083125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9476839124978401948722083 14215258687467602923083125)
                    ·
                      refine ⟨1332680501950087774039043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14215258687467602923083125 1332680501950087774039043)
                      ·
                        rfl

theorem cell23_2595386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_2595386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595386 prefixEnd_2595386 := by exact prefixLift 2595386
  have htrace : WordTrace (prefixWord ++ tailWord_2595386) baseStart_2595386 baseEnd_2595386 := by
    simpa [prefixWord, tailWord_2595386, baseEnd_2595386] using wordTrace_append hprefix tailTrace_2595386
  have hstable : (prefixWord ++ tailWord_2595386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595386).length < 2 ^ (prefixWord ++ tailWord_2595386).sum := by decide
  have hdescent : baseEnd_2595386 < baseStart_2595386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595389 : List Nat := [1, 4, 1, 3, 2, 1, 11]
def baseStart_2595389 : Nat := 118140960795 + 2595389 * 2 ^ 59
def prefixEnd_2595389 : Nat := 4983230072969 + 3 ^ 40 * 2595389 * 2
def baseEnd_2595389 : Nat := 16452864720889521756809

theorem tailTrace_2595389 : CollatzResearch.WordTrace tailWord_2595389 prefixEnd_2595389 16452864720889521756809 := by
  unfold tailWord_2595389
  simp only [CollatzResearch.WordTrace]
  refine ⟨94661613594356384996805221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63107742396237589997870147 94661613594356384996805221)
  ·
    refine ⟨17749052548941822186900979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94661613594356384996805221 17749052548941822186900979)
    ·
      refine ⟨26623578823412733280351469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17749052548941822186900979 26623578823412733280351469)
      ·
        refine ⟨9983842058779774980131801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26623578823412733280351469 9983842058779774980131801)
        ·
          refine ⟨7487881544084831235098851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9983842058779774980131801 7487881544084831235098851)
          ·
            refine ⟨11231822316127246852648277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7487881544084831235098851 11231822316127246852648277)
            ·
              refine ⟨16452864720889521756809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11231822316127246852648277 16452864720889521756809)
              ·
                rfl

theorem cell23_2595389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 11].length) (baseStart_2595389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595389 prefixEnd_2595389 := by exact prefixLift 2595389
  have htrace : WordTrace (prefixWord ++ tailWord_2595389) baseStart_2595389 baseEnd_2595389 := by
    simpa [prefixWord, tailWord_2595389, baseEnd_2595389] using wordTrace_append hprefix tailTrace_2595389
  have hstable : (prefixWord ++ tailWord_2595389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595389).length < 2 ^ (prefixWord ++ tailWord_2595389).sum := by decide
  have hdescent : baseEnd_2595389 < baseStart_2595389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595400 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_2595400 : Nat := 118140960795 + 2595400 * 2 ^ 59
def prefixEnd_2595400 : Nat := 4983230072969 + 3 ^ 40 * 2595400 * 2
def baseEnd_2595400 : Nat := 1332687690679250719263979

theorem tailTrace_2595400 : CollatzResearch.WordTrace tailWord_2595400 prefixEnd_2595400 1332687690679250719263979 := by
  unfold tailWord_2595400
  simp only [CollatzResearch.WordTrace]
  refine ⟨47331007398658266937727827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63108009864877689250303769 47331007398658266937727827)
  ·
    refine ⟨70996511097987400406591741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47331007398658266937727827 70996511097987400406591741)
    ·
      refine ⟨26623691661745275152471903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70996511097987400406591741 26623691661745275152471903)
      ·
        refine ⟨39935537492617912728707855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26623691661745275152471903 39935537492617912728707855)
        ·
          refine ⟨59903306238926869093061783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39935537492617912728707855 59903306238926869093061783)
          ·
            refine ⟨89854959358390303639592675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59903306238926869093061783 89854959358390303639592675)
            ·
              refine ⟨134782439037585455459389013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89854959358390303639592675 134782439037585455459389013)
              ·
                refine ⟨1579481707471704556164715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 134782439037585455459389013 1579481707471704556164715)
                ·
                  refine ⟨2369222561207556834247073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579481707471704556164715 2369222561207556834247073)
                  ·
                    refine ⟨1776916920905667625685305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369222561207556834247073 1776916920905667625685305)
                    ·
                      refine ⟨1332687690679250719263979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776916920905667625685305 1332687690679250719263979)
                      ·
                        rfl

theorem cell23_2595400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_2595400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595400 prefixEnd_2595400 := by exact prefixLift 2595400
  have htrace : WordTrace (prefixWord ++ tailWord_2595400) baseStart_2595400 baseEnd_2595400 := by
    simpa [prefixWord, tailWord_2595400, baseEnd_2595400] using wordTrace_append hprefix tailTrace_2595400
  have hstable : (prefixWord ++ tailWord_2595400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595400).length < 2 ^ (prefixWord ++ tailWord_2595400).sum := by decide
  have hdescent : baseEnd_2595400 < baseStart_2595400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595459 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2595459 : Nat := 118140960795 + 2595459 * 2 ^ 59
def prefixEnd_2595459 : Nat := 4983230072969 + 3 ^ 40 * 2595459 * 2
def baseEnd_2595459 : Nat := 1332717986037865988426207

theorem tailTrace_2595459 : CollatzResearch.WordTrace tailWord_2595459 prefixEnd_2595459 1332717986037865988426207 := by
  unfold tailWord_2595459
  simp only [CollatzResearch.WordTrace]
  refine ⟨94664166704102786951853431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63109444469401857967902287 94664166704102786951853431)
  ·
    refine ⟨141996250056154180427780147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94664166704102786951853431 141996250056154180427780147)
    ·
      refine ⟨212994375084231270641670221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141996250056154180427780147 212994375084231270641670221)
      ·
        refine ⟨79872890656586726490626333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212994375084231270641670221 79872890656586726490626333)
        ·
          refine ⟨29952333996220022433984875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79872890656586726490626333 29952333996220022433984875)
          ·
            refine ⟨44928500994330033650977313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29952333996220022433984875 44928500994330033650977313)
            ·
              refine ⟨33696375745747525238232985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44928500994330033650977313 33696375745747525238232985)
              ·
                refine ⟨25272281809310643928674739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33696375745747525238232985 25272281809310643928674739)
                ·
                  refine ⟨37908422713965965893012109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25272281809310643928674739 37908422713965965893012109)
                  ·
                    refine ⟨14215658517737237209879541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37908422713965965893012109 14215658517737237209879541)
                    ·
                      refine ⟨1332717986037865988426207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14215658517737237209879541 1332717986037865988426207)
                      ·
                        rfl

theorem cell23_2595459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2595459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595459 prefixEnd_2595459 := by exact prefixLift 2595459
  have htrace : WordTrace (prefixWord ++ tailWord_2595459) baseStart_2595459 baseEnd_2595459 := by
    simpa [prefixWord, tailWord_2595459, baseEnd_2595459] using wordTrace_append hprefix tailTrace_2595459
  have hstable : (prefixWord ++ tailWord_2595459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595459).length < 2 ^ (prefixWord ++ tailWord_2595459).sum := by decide
  have hdescent : baseEnd_2595459 < baseStart_2595459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595507 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 2, 2, 2]
def baseStart_2595507 : Nat := 118140960795 + 2595507 * 2 ^ 59
def prefixEnd_2595507 : Nat := 4983230072969 + 3 ^ 40 * 2595507 * 2
def baseEnd_2595507 : Nat := 1332742633109281800625987

theorem tailTrace_2595507 : CollatzResearch.WordTrace tailWord_2595507 prefixEnd_2595507 1332742633109281800625987 := by
  unfold tailWord_2595507
  simp only [CollatzResearch.WordTrace]
  refine ⟨94665917407928891149600775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63110611605285927433067183 94665917407928891149600775)
  ·
    refine ⟨141998876111893336724401163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94665917407928891149600775 141998876111893336724401163)
    ·
      refine ⟨212998314167840005086601745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141998876111893336724401163 212998314167840005086601745)
      ·
        refine ⟨159748735625880003814951309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212998314167840005086601745 159748735625880003814951309)
        ·
          refine ⟨59905775859705001430606741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159748735625880003814951309 59905775859705001430606741)
          ·
            refine ⟨2808083243423671942059691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59905775859705001430606741 2808083243423671942059691)
            ·
              refine ⟨4212124865135507913089537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808083243423671942059691 4212124865135507913089537)
              ·
                refine ⟨3159093648851630934817153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212124865135507913089537 3159093648851630934817153)
                ·
                  refine ⟨2369320236638723201112865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159093648851630934817153 2369320236638723201112865)
                  ·
                    refine ⟨1776990177479042400834649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369320236638723201112865 1776990177479042400834649)
                    ·
                      refine ⟨1332742633109281800625987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776990177479042400834649 1332742633109281800625987)
                      ·
                        rfl

theorem cell23_2595507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 2, 2].length) (baseStart_2595507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595507 prefixEnd_2595507 := by exact prefixLift 2595507
  have htrace : WordTrace (prefixWord ++ tailWord_2595507) baseStart_2595507 baseEnd_2595507 := by
    simpa [prefixWord, tailWord_2595507, baseEnd_2595507] using wordTrace_append hprefix tailTrace_2595507
  have hstable : (prefixWord ++ tailWord_2595507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595507).length < 2 ^ (prefixWord ++ tailWord_2595507).sum := by decide
  have hdescent : baseEnd_2595507 < baseStart_2595507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595524 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_2595524 : Nat := 118140960795 + 2595524 * 2 ^ 59
def prefixEnd_2595524 : Nat := 4983230072969 + 3 ^ 40 * 2595524 * 2
def baseEnd_2595524 : Nat := 1332751362280408234113409

theorem tailTrace_2595524 : CollatzResearch.WordTrace tailWord_2595524 prefixEnd_2595524 1332751362280408234113409 := by
  unfold tailWord_2595524
  simp only [CollatzResearch.WordTrace]
  refine ⟨47333268724433651526484813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63111024965911535368646417 47333268724433651526484813)
  ·
    refine ⟨17749975771662619322431805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47333268724433651526484813 17749975771662619322431805)
    ·
      refine ⟨6656240914373482245911927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17749975771662619322431805 6656240914373482245911927)
      ·
        refine ⟨9984361371560223368867891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6656240914373482245911927 9984361371560223368867891)
        ·
          refine ⟨14976542057340335053301837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9984361371560223368867891 14976542057340335053301837)
          ·
            refine ⟨5616203271502625644988189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14976542057340335053301837 5616203271502625644988189)
            ·
              refine ⟨2106076226813484616870571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5616203271502625644988189 2106076226813484616870571)
              ·
                refine ⟨3159114340220226925305857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106076226813484616870571 3159114340220226925305857)
                ·
                  refine ⟨2369335755165170193979393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159114340220226925305857 2369335755165170193979393)
                  ·
                    refine ⟨1777001816373877645484545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369335755165170193979393 1777001816373877645484545)
                    ·
                      refine ⟨1332751362280408234113409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777001816373877645484545 1332751362280408234113409)
                      ·
                        rfl

theorem cell23_2595524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_2595524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595524 prefixEnd_2595524 := by exact prefixLift 2595524
  have htrace : WordTrace (prefixWord ++ tailWord_2595524) baseStart_2595524 baseEnd_2595524 := by
    simpa [prefixWord, tailWord_2595524, baseEnd_2595524] using wordTrace_append hprefix tailTrace_2595524
  have hstable : (prefixWord ++ tailWord_2595524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595524).length < 2 ^ (prefixWord ++ tailWord_2595524).sum := by decide
  have hdescent : baseEnd_2595524 < baseStart_2595524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595546 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2595546 : Nat := 118140960795 + 2595546 * 2 ^ 59
def prefixEnd_2595546 : Nat := 4983230072969 + 3 ^ 40 * 2595546 * 2
def baseEnd_2595546 : Nat := 1332762658854807148038307

theorem tailTrace_2595546 : CollatzResearch.WordTrace tailWord_2595546 prefixEnd_2595546 1332762658854807148038307 := by
  unfold tailWord_2595546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23666834963696900202567623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63111559903191733873513661 23666834963696900202567623)
  ·
    refine ⟨35500252445545350303851435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23666834963696900202567623 35500252445545350303851435)
    ·
      refine ⟨53250378668318025455777153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35500252445545350303851435 53250378668318025455777153)
      ·
        refine ⟨39937784001238519091832865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53250378668318025455777153 39937784001238519091832865)
        ·
          refine ⟨29953338000928889318874649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39937784001238519091832865 29953338000928889318874649)
          ·
            refine ⟨22465003500696666989155987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29953338000928889318874649 22465003500696666989155987)
            ·
              refine ⟨33697505251045000483733981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22465003500696666989155987 33697505251045000483733981)
              ·
                refine ⟨12636564469141875181400243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33697505251045000483733981 12636564469141875181400243)
                ·
                  refine ⟨18954846703712812772100365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12636564469141875181400243 18954846703712812772100365)
                  ·
                    refine ⟨7108067513892304789537637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18954846703712812772100365 7108067513892304789537637)
                    ·
                      refine ⟨1332762658854807148038307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7108067513892304789537637 1332762658854807148038307)
                      ·
                        rfl

theorem cell23_2595546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2595546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595546 prefixEnd_2595546 := by exact prefixLift 2595546
  have htrace : WordTrace (prefixWord ++ tailWord_2595546) baseStart_2595546 baseEnd_2595546 := by
    simpa [prefixWord, tailWord_2595546, baseEnd_2595546] using wordTrace_append hprefix tailTrace_2595546
  have hstable : (prefixWord ++ tailWord_2595546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595546).length < 2 ^ (prefixWord ++ tailWord_2595546).sum := by decide
  have hdescent : baseEnd_2595546 < baseStart_2595546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595620 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 6]
def baseStart_2595620 : Nat := 118140960795 + 2595620 * 2 ^ 59
def prefixEnd_2595620 : Nat := 4983230072969 + 3 ^ 40 * 2595620 * 2
def baseEnd_2595620 : Nat := 148088961824804428723663

theorem tailTrace_2595620 : CollatzResearch.WordTrace tailWord_2595620 prefixEnd_2595620 148088961824804428723663 := by
  unfold tailWord_2595620
  simp only [CollatzResearch.WordTrace]
  refine ⟨47335019428259755724232157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63113359237679674298976209 47335019428259755724232157)
  ·
    refine ⟨17750632285597408396587059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47335019428259755724232157 17750632285597408396587059)
    ·
      refine ⟨26625948428396112594880589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17750632285597408396587059 26625948428396112594880589)
      ·
        refine ⟨9984730660648542223080221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26625948428396112594880589 9984730660648542223080221)
        ·
          refine ⟨3744273997743203333655083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9984730660648542223080221 3744273997743203333655083)
          ·
            refine ⟨5616410996614805000482625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744273997743203333655083 5616410996614805000482625)
            ·
              refine ⟨4212308247461103750361969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616410996614805000482625 4212308247461103750361969)
              ·
                refine ⟨3159231185595827812771477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212308247461103750361969 3159231185595827812771477)
                ·
                  refine ⟨148088961824804428723663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3159231185595827812771477 148088961824804428723663)
                  ·
                    rfl

theorem cell23_2595620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_2595620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595620 prefixEnd_2595620 := by exact prefixLift 2595620
  have htrace : WordTrace (prefixWord ++ tailWord_2595620) baseStart_2595620 baseEnd_2595620 := by
    simpa [prefixWord, tailWord_2595620, baseEnd_2595620] using wordTrace_append hprefix tailTrace_2595620
  have hstable : (prefixWord ++ tailWord_2595620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595620).length < 2 ^ (prefixWord ++ tailWord_2595620).sum := by decide
  have hdescent : baseEnd_2595620 < baseStart_2595620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595653 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 8, 2]
def baseStart_2595653 : Nat := 118140960795 + 2595653 * 2 ^ 59
def prefixEnd_2595653 : Nat := 4983230072969 + 3 ^ 40 * 2595653 * 2
def baseEnd_2595653 : Nat := 1332817601284838229400315

theorem tailTrace_2595653 : CollatzResearch.WordTrace tailWord_2595653 prefixEnd_2595653 1332817601284838229400315 := by
  unfold tailWord_2595653
  simp only [CollatzResearch.WordTrace]
  refine ⟨94671242465399958084415613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63114161643599972056277075 94671242465399958084415613)
  ·
    refine ⟨35501715924524984281655855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94671242465399958084415613 35501715924524984281655855)
    ·
      refine ⟨53252573886787476422483783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35501715924524984281655855 53252573886787476422483783)
      ·
        refine ⟨79878860830181214633725675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53252573886787476422483783 79878860830181214633725675)
        ·
          refine ⟨119818291245271821950588513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79878860830181214633725675 119818291245271821950588513)
          ·
            refine ⟨89863718433953866462941385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119818291245271821950588513 89863718433953866462941385)
            ·
              refine ⟨67397788825465399847206039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89863718433953866462941385 67397788825465399847206039)
              ·
                refine ⟨101096683238198099770809059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67397788825465399847206039 101096683238198099770809059)
                ·
                  refine ⟨151645024857297149656213589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101096683238198099770809059 151645024857297149656213589)
                  ·
                    refine ⟨1777090135046450972533753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 151645024857297149656213589 1777090135046450972533753)
                    ·
                      refine ⟨1332817601284838229400315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777090135046450972533753 1332817601284838229400315)
                      ·
                        rfl

theorem cell23_2595653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_2595653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595653 prefixEnd_2595653 := by exact prefixLift 2595653
  have htrace : WordTrace (prefixWord ++ tailWord_2595653) baseStart_2595653 baseEnd_2595653 := by
    simpa [prefixWord, tailWord_2595653, baseEnd_2595653] using wordTrace_append hprefix tailTrace_2595653
  have hstable : (prefixWord ++ tailWord_2595653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595653).length < 2 ^ (prefixWord ++ tailWord_2595653).sum := by decide
  have hdescent : baseEnd_2595653 < baseStart_2595653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595657 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 2, 3, 2]
def baseStart_2595657 : Nat := 118140960795 + 2595657 * 2 ^ 59
def prefixEnd_2595657 : Nat := 4983230072969 + 3 ^ 40 * 2595657 * 2
def baseEnd_2595657 : Nat := 1332819655207456213750297

theorem tailTrace_2595657 : CollatzResearch.WordTrace tailWord_2595657 prefixEnd_2595657 1332819655207456213750297 := by
  unfold tailWord_2595657
  simp only [CollatzResearch.WordTrace]
  refine ⟨94671388357385466767561225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63114258904923644511707483 94671388357385466767561225)
  ·
    refine ⟨71003541268039100075670919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94671388357385466767561225 71003541268039100075670919)
    ·
      refine ⟨106505311902058650113506379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71003541268039100075670919 106505311902058650113506379)
      ·
        refine ⟨159757967853087975170259569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106505311902058650113506379 159757967853087975170259569)
        ·
          refine ⟨119818475889815981377694677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159757967853087975170259569 119818475889815981377694677)
          ·
            refine ⟨2808245528667562063539719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 119818475889815981377694677 2808245528667562063539719)
            ·
              refine ⟨4212368293001343095309579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808245528667562063539719 4212368293001343095309579)
              ·
                refine ⟨6318552439502014642964369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4212368293001343095309579 6318552439502014642964369)
                ·
                  refine ⟨4738914329626510982223277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6318552439502014642964369 4738914329626510982223277)
                  ·
                    refine ⟨1777092873609941618333729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4738914329626510982223277 1777092873609941618333729)
                    ·
                      refine ⟨1332819655207456213750297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777092873609941618333729 1332819655207456213750297)
                      ·
                        rfl

theorem cell23_2595657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 3, 2].length) (baseStart_2595657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595657 prefixEnd_2595657 := by exact prefixLift 2595657
  have htrace : WordTrace (prefixWord ++ tailWord_2595657) baseStart_2595657 baseEnd_2595657 := by
    simpa [prefixWord, tailWord_2595657, baseEnd_2595657] using wordTrace_append hprefix tailTrace_2595657
  have hstable : (prefixWord ++ tailWord_2595657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595657).length < 2 ^ (prefixWord ++ tailWord_2595657).sum := by decide
  have hdescent : baseEnd_2595657 < baseStart_2595657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595687 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_2595687 : Nat := 118140960795 + 2595687 * 2 ^ 59
def prefixEnd_2595687 : Nat := 4983230072969 + 3 ^ 40 * 2595687 * 2
def baseEnd_2595687 : Nat := 1332835059627091096375159

theorem tailTrace_2595687 : CollatzResearch.WordTrace tailWord_2595687 prefixEnd_2595687 1332835059627091096375159 := by
  unfold tailWord_2595687
  simp only [CollatzResearch.WordTrace]
  refine ⟨94672482547276781891153315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63114988364851187927435543 94672482547276781891153315)
  ·
    refine ⟨142008723820915172836729973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94672482547276781891153315 142008723820915172836729973)
    ·
      refine ⟨13313317858210797453443435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142008723820915172836729973 13313317858210797453443435)
      ·
        refine ⟨19969976787316196180165153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13313317858210797453443435 19969976787316196180165153)
        ·
          refine ⟨14977482590487147135123865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19969976787316196180165153 14977482590487147135123865)
          ·
            refine ⟨11233111942865360351342899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14977482590487147135123865 11233111942865360351342899)
            ·
              refine ⟨16849667914298040527014349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11233111942865360351342899 16849667914298040527014349)
              ·
                refine ⟨6318625467861765197630381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16849667914298040527014349 6318625467861765197630381)
                ·
                  refine ⟨2369484550448161949111393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6318625467861765197630381 2369484550448161949111393)
                  ·
                    refine ⟨1777113412836121461833545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369484550448161949111393 1777113412836121461833545)
                    ·
                      refine ⟨1332835059627091096375159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777113412836121461833545 1332835059627091096375159)
                      ·
                        rfl

theorem cell23_2595687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_2595687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595687 prefixEnd_2595687 := by exact prefixLift 2595687
  have htrace : WordTrace (prefixWord ++ tailWord_2595687) baseStart_2595687 baseEnd_2595687 := by
    simpa [prefixWord, tailWord_2595687, baseEnd_2595687] using wordTrace_append hprefix tailTrace_2595687
  have hstable : (prefixWord ++ tailWord_2595687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595687).length < 2 ^ (prefixWord ++ tailWord_2595687).sum := by decide
  have hdescent : baseEnd_2595687 < baseStart_2595687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595697 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 2, 4]
def baseStart_2595697 : Nat := 118140960795 + 2595697 * 2 ^ 59
def prefixEnd_2595697 : Nat := 4983230072969 + 3 ^ 40 * 2595697 * 2
def baseEnd_2595697 : Nat := 444280064811212019083371

theorem tailTrace_2595697 : CollatzResearch.WordTrace tailWord_2595697 prefixEnd_2595697 444280064811212019083371 := by
  unfold tailWord_2595697
  simp only [CollatzResearch.WordTrace]
  refine ⟨94672847277240553599017345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63115231518160369066011563 94672847277240553599017345)
  ·
    refine ⟨71004635457930415199263009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94672847277240553599017345 71004635457930415199263009)
    ·
      refine ⟨53253476593447811399447257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71004635457930415199263009 53253476593447811399447257)
      ·
        refine ⟨39940107445085858549585443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53253476593447811399447257 39940107445085858549585443)
        ·
          refine ⟨59910161167628787824378165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39940107445085858549585443 59910161167628787824378165)
          ·
            refine ⟨5616577609465198858535453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59910161167628787824378165 5616577609465198858535453)
            ·
              refine ⟨2106216603549449571950795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5616577609465198858535453 2106216603549449571950795)
              ·
                refine ⟨3159324905324174357926193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106216603549449571950795 3159324905324174357926193)
                ·
                  refine ⟨2369493678993130768444645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159324905324174357926193 2369493678993130768444645)
                  ·
                    refine ⟨444280064811212019083371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2369493678993130768444645 444280064811212019083371)
                    ·
                      rfl

theorem cell23_2595697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_2595697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595697 prefixEnd_2595697 := by exact prefixLift 2595697
  have htrace : WordTrace (prefixWord ++ tailWord_2595697) baseStart_2595697 baseEnd_2595697 := by
    simpa [prefixWord, tailWord_2595697, baseEnd_2595697] using wordTrace_append hprefix tailTrace_2595697
  have hstable : (prefixWord ++ tailWord_2595697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595697).length < 2 ^ (prefixWord ++ tailWord_2595697).sum := by decide
  have hdescent : baseEnd_2595697 < baseStart_2595697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595721 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 1, 2, 2]
def baseStart_2595721 : Nat := 118140960795 + 2595721 * 2 ^ 59
def prefixEnd_2595721 : Nat := 4983230072969 + 3 ^ 40 * 2595721 * 2
def baseEnd_2595721 : Nat := 1332852517969343963350003

theorem tailTrace_2595721 : CollatzResearch.WordTrace tailWord_2595721 prefixEnd_2595721 1332852517969343963350003 := by
  unfold tailWord_2595721
  simp only [CollatzResearch.WordTrace]
  refine ⟨94673722629153605697891017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63115815086102403798594011 94673722629153605697891017)
  ·
    refine ⟨71005291971865204273418263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94673722629153605697891017 71005291971865204273418263)
    ·
      refine ⟨106507937957797806410127395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71005291971865204273418263 106507937957797806410127395)
      ·
        refine ⟨159761906936696709615191093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106507937957797806410127395 159761906936696709615191093)
        ·
          refine ⟨14977678775315316526424165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159761906936696709615191093 14977678775315316526424165)
          ·
            refine ⟨2808314770371621848704531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14977678775315316526424165 2808314770371621848704531)
            ·
              refine ⟨4212472155557432773056797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808314770371621848704531 4212472155557432773056797)
              ·
                refine ⟨1579677058334037289896299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4212472155557432773056797 1579677058334037289896299)
                ·
                  refine ⟨2369515587501055934844449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579677058334037289896299 2369515587501055934844449)
                  ·
                    refine ⟨1777136690625791951133337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369515587501055934844449 1777136690625791951133337)
                    ·
                      refine ⟨1332852517969343963350003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777136690625791951133337 1332852517969343963350003)
                      ·
                        rfl

theorem cell23_2595721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 2, 2].length) (baseStart_2595721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595721 prefixEnd_2595721 := by exact prefixLift 2595721
  have htrace : WordTrace (prefixWord ++ tailWord_2595721) baseStart_2595721 baseEnd_2595721 := by
    simpa [prefixWord, tailWord_2595721, baseEnd_2595721] using wordTrace_append hprefix tailTrace_2595721
  have hstable : (prefixWord ++ tailWord_2595721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595721).length < 2 ^ (prefixWord ++ tailWord_2595721).sum := by decide
  have hdescent : baseEnd_2595721 < baseStart_2595721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595738 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2595738 : Nat := 118140960795 + 2595738 * 2 ^ 59
def prefixEnd_2595738 : Nat := 4983230072969 + 3 ^ 40 * 2595738 * 2
def baseEnd_2595738 : Nat := 1332861247140470396837425

theorem tailTrace_2595738 : CollatzResearch.WordTrace tailWord_2595738 prefixEnd_2595738 1332861247140470396837425 := by
  unfold tailWord_2595738
  simp only [CollatzResearch.WordTrace]
  refine ⟨23668585667523004400314967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63116228446728011734173245 23668585667523004400314967)
  ·
    refine ⟨35502878501284506600472451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23668585667523004400314967 35502878501284506600472451)
    ·
      refine ⟨53254317751926759900708677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35502878501284506600472451 53254317751926759900708677)
      ·
        refine ⟨9985184578486267481382877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53254317751926759900708677 9985184578486267481382877)
        ·
          refine ⟨3744444216932350305518579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9985184578486267481382877 3744444216932350305518579)
          ·
            refine ⟨5616666325398525458277869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744444216932350305518579 5616666325398525458277869)
            ·
              refine ⟨2106249872024447046854201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5616666325398525458277869 2106249872024447046854201)
              ·
                refine ⟨1579687404018335285140651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106249872024447046854201 1579687404018335285140651)
                ·
                  refine ⟨2369531106027502927710977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579687404018335285140651 2369531106027502927710977)
                  ·
                    refine ⟨1777148329520627195783233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369531106027502927710977 1777148329520627195783233)
                    ·
                      refine ⟨1332861247140470396837425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777148329520627195783233 1332861247140470396837425)
                      ·
                        rfl

theorem cell23_2595738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2595738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595738 prefixEnd_2595738 := by exact prefixLift 2595738
  have htrace : WordTrace (prefixWord ++ tailWord_2595738) baseStart_2595738 baseEnd_2595738 := by
    simpa [prefixWord, tailWord_2595738, baseEnd_2595738] using wordTrace_append hprefix tailTrace_2595738
  have hstable : (prefixWord ++ tailWord_2595738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595738).length < 2 ^ (prefixWord ++ tailWord_2595738).sum := by decide
  have hdescent : baseEnd_2595738 < baseStart_2595738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595763 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 3]
def baseStart_2595763 : Nat := 118140960795 + 2595763 * 2 ^ 59
def prefixEnd_2595763 : Nat := 4983230072969 + 3 ^ 40 * 2595763 * 2
def baseEnd_2595763 : Nat := 1332874084156832799024809

theorem tailTrace_2595763 : CollatzResearch.WordTrace tailWord_2595763 prefixEnd_2595763 1332874084156832799024809 := by
  unfold tailWord_2595763
  simp only [CollatzResearch.WordTrace]
  refine ⟨94675254495001446870919943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63116836330000964580613295 94675254495001446870919943)
  ·
    refine ⟨142012881742502170306379915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94675254495001446870919943 142012881742502170306379915)
    ·
      refine ⟨213019322613753255459569873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142012881742502170306379915 213019322613753255459569873)
      ·
        refine ⟨159764491960314941594677405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213019322613753255459569873 159764491960314941594677405)
        ·
          refine ⟨59911684485118103098004027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159764491960314941594677405 59911684485118103098004027)
          ·
            refine ⟨89867526727677154647006041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59911684485118103098004027 89867526727677154647006041)
            ·
              refine ⟨67400645045757865985254531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89867526727677154647006041 67400645045757865985254531)
              ·
                refine ⟨101100967568636798977881797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67400645045757865985254531 101100967568636798977881797)
                ·
                  refine ⟨18956431419119399808352837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101100967568636798977881797 18956431419119399808352837)
                  ·
                    refine ⟨3554330891084887464066157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18956431419119399808352837 3554330891084887464066157)
                    ·
                      refine ⟨1332874084156832799024809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3554330891084887464066157 1332874084156832799024809)
                      ·
                        rfl

theorem cell23_2595763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_2595763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595763 prefixEnd_2595763 := by exact prefixLift 2595763
  have htrace : WordTrace (prefixWord ++ tailWord_2595763) baseStart_2595763 baseEnd_2595763 := by
    simpa [prefixWord, tailWord_2595763, baseEnd_2595763] using wordTrace_append hprefix tailTrace_2595763
  have hstable : (prefixWord ++ tailWord_2595763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595763).length < 2 ^ (prefixWord ++ tailWord_2595763).sum := by decide
  have hdescent : baseEnd_2595763 < baseStart_2595763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595789 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2595789 : Nat := 118140960795 + 2595789 * 2 ^ 59
def prefixEnd_2595789 : Nat := 4983230072969 + 3 ^ 40 * 2595789 * 2
def baseEnd_2595789 : Nat := 1332887434653849697299691

theorem tailTrace_2595789 : CollatzResearch.WordTrace tailWord_2595789 prefixEnd_2595789 1332887434653849697299691 := by
  unfold tailWord_2595789
  simp only [CollatzResearch.WordTrace]
  refine ⟨94676202792907253311366421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63117468528604835540910947 94676202792907253311366421)
  ·
    refine ⟨4437947005917527498970301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94676202792907253311366421 4437947005917527498970301)
    ·
      refine ⟨1664230127219072812113863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4437947005917527498970301 1664230127219072812113863)
      ·
        refine ⟨2496345190828609218170795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664230127219072812113863 2496345190828609218170795)
        ·
          refine ⟨3744517786242913827256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496345190828609218170795 3744517786242913827256193)
          ·
            refine ⟨2808388339682185370442145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3744517786242913827256193 2808388339682185370442145)
            ·
              refine ⟨2106291254761639027831609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808388339682185370442145 2106291254761639027831609)
              ·
                refine ⟨1579718441071229270873707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106291254761639027831609 1579718441071229270873707)
                ·
                  refine ⟨2369577661606843906310561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579718441071229270873707 2369577661606843906310561)
                  ·
                    refine ⟨1777183246205132929732921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369577661606843906310561 1777183246205132929732921)
                    ·
                      refine ⟨1332887434653849697299691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777183246205132929732921 1332887434653849697299691)
                      ·
                        rfl

theorem cell23_2595789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2595789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595789 prefixEnd_2595789 := by exact prefixLift 2595789
  have htrace : WordTrace (prefixWord ++ tailWord_2595789) baseStart_2595789 baseEnd_2595789 := by
    simpa [prefixWord, tailWord_2595789, baseEnd_2595789] using wordTrace_append hprefix tailTrace_2595789
  have hstable : (prefixWord ++ tailWord_2595789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595789).length < 2 ^ (prefixWord ++ tailWord_2595789).sum := by decide
  have hdescent : baseEnd_2595789 < baseStart_2595789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595911 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 1, 4]
def baseStart_2595911 : Nat := 118140960795 + 2595911 * 2 ^ 59
def prefixEnd_2595911 : Nat := 4983230072969 + 3 ^ 40 * 2595911 * 2
def baseEnd_2595911 : Nat := 444316693097899406658043

theorem tailTrace_2595911 : CollatzResearch.WordTrace tailWord_2595911 prefixEnd_2595911 444316693097899406658043 := by
  unfold tailWord_2595911
  simp only [CollatzResearch.WordTrace]
  refine ⟨94680652498465268147307587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63120434998976845431538391 94680652498465268147307587)
  ·
    refine ⟨142020978747697902220961381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94680652498465268147307587 142020978747697902220961381)
    ·
      refine ⟨26628933515193356666430259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142020978747697902220961381 26628933515193356666430259)
      ·
        refine ⟨39943400272790034999645389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26628933515193356666430259 39943400272790034999645389)
        ·
          refine ⟨14978775102296263124867021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39943400272790034999645389 14978775102296263124867021)
          ·
            refine ⟨5617040663361098671825133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14978775102296263124867021 5617040663361098671825133)
            ·
              refine ⟨2106390248760412001934425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5617040663361098671825133 2106390248760412001934425)
              ·
                refine ⟨1579792686570309001450819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106390248760412001934425 1579792686570309001450819)
                ·
                  refine ⟨2369689029855463502176229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579792686570309001450819 2369689029855463502176229)
                  ·
                    refine ⟨444316693097899406658043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2369689029855463502176229 444316693097899406658043)
                    ·
                      rfl

theorem cell23_2595911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_2595911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595911 prefixEnd_2595911 := by exact prefixLift 2595911
  have htrace : WordTrace (prefixWord ++ tailWord_2595911) baseStart_2595911 baseEnd_2595911 := by
    simpa [prefixWord, tailWord_2595911, baseEnd_2595911] using wordTrace_append hprefix tailTrace_2595911
  have hstable : (prefixWord ++ tailWord_2595911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595911).length < 2 ^ (prefixWord ++ tailWord_2595911).sum := by decide
  have hdescent : baseEnd_2595911 < baseStart_2595911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595927 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 6, 3, 2]
def baseStart_2595927 : Nat := 118140960795 + 2595927 * 2 ^ 59
def prefixEnd_2595927 : Nat := 4983230072969 + 3 ^ 40 * 2595927 * 2
def baseEnd_2595927 : Nat := 1332958294984170157374055

theorem tailTrace_2595927 : CollatzResearch.WordTrace tailWord_2595927 prefixEnd_2595927 1332958294984170157374055 := by
  unfold tailWord_2595927
  simp only [CollatzResearch.WordTrace]
  refine ⟨94681236066407302879890035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63120824044271535253260023 94681236066407302879890035)
  ·
    refine ⟨142021854099610954319835053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94681236066407302879890035 142021854099610954319835053)
    ·
      refine ⟨53258195287354107869938145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142021854099610954319835053 53258195287354107869938145)
      ·
        refine ⟨39943646465515580902453609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53258195287354107869938145 39943646465515580902453609)
        ·
          refine ⟨29957734849136685676840207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39943646465515580902453609 29957734849136685676840207)
          ·
            refine ⟨44936602273705028515260311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29957734849136685676840207 44936602273705028515260311)
            ·
              refine ⟨67404903410557542772890467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44936602273705028515260311 67404903410557542772890467)
              ·
                refine ⟨101107355115836314159335701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67404903410557542772890467 101107355115836314159335701)
                ·
                  refine ⟨4739407271054827226218861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101107355115836314159335701 4739407271054827226218861)
                  ·
                    refine ⟨1777277726645560209832073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4739407271054827226218861 1777277726645560209832073)
                    ·
                      refine ⟨1332958294984170157374055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777277726645560209832073 1332958294984170157374055)
                      ·
                        rfl

theorem cell23_2595927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_2595927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595927 prefixEnd_2595927 := by exact prefixLift 2595927
  have htrace : WordTrace (prefixWord ++ tailWord_2595927) baseStart_2595927 baseEnd_2595927 := by
    simpa [prefixWord, tailWord_2595927, baseEnd_2595927] using wordTrace_append hprefix tailTrace_2595927
  have hstable : (prefixWord ++ tailWord_2595927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595927).length < 2 ^ (prefixWord ++ tailWord_2595927).sum := by decide
  have hdescent : baseEnd_2595927 < baseStart_2595927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595937 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2595937 : Nat := 118140960795 + 2595937 * 2 ^ 59
def prefixEnd_2595937 : Nat := 4983230072969 + 3 ^ 40 * 2595937 * 2
def baseEnd_2595937 : Nat := 444321143263571706083003

theorem tailTrace_2595937 : CollatzResearch.WordTrace tailWord_2595937 prefixEnd_2595937 444321143263571706083003 := by
  unfold tailWord_2595937
  simp only [CollatzResearch.WordTrace]
  refine ⟨94681600796371074587754065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63121067197580716391836043 94681600796371074587754065)
  ·
    refine ⟨71011200597278305940815549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94681600796371074587754065 71011200597278305940815549)
    ·
      refine ⟨26629200223979364727805831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71011200597278305940815549 26629200223979364727805831)
      ·
        refine ⟨39943800335969047091708747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26629200223979364727805831 39943800335969047091708747)
        ·
          refine ⟨59915700503953570637563121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39943800335969047091708747 59915700503953570637563121)
          ·
            refine ⟨44936775377965177978172341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59915700503953570637563121 44936775377965177978172341)
            ·
              refine ⟨4212822691684235435453657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44936775377965177978172341 4212822691684235435453657)
              ·
                refine ⟨3159617018763176576590243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212822691684235435453657 3159617018763176576590243)
                ·
                  refine ⟨4739425528144764864885365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159617018763176576590243 4739425528144764864885365)
                  ·
                    refine ⟨444321143263571706083003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4739425528144764864885365 444321143263571706083003)
                    ·
                      rfl

theorem cell23_2595937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2595937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595937 prefixEnd_2595937 := by exact prefixLift 2595937
  have htrace : WordTrace (prefixWord ++ tailWord_2595937) baseStart_2595937 baseEnd_2595937 := by
    simpa [prefixWord, tailWord_2595937, baseEnd_2595937] using wordTrace_append hprefix tailTrace_2595937
  have hstable : (prefixWord ++ tailWord_2595937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595937).length < 2 ^ (prefixWord ++ tailWord_2595937).sum := by decide
  have hdescent : baseEnd_2595937 < baseStart_2595937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595954 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_2595954 : Nat := 118140960795 + 2595954 * 2 ^ 59
def prefixEnd_2595954 : Nat := 4983230072969 + 3 ^ 40 * 2595954 * 2
def baseEnd_2595954 : Nat := 444324052987280517245477

theorem tailTrace_2595954 : CollatzResearch.WordTrace tailWord_2595954 prefixEnd_2595954 444324052987280517245477 := by
  unfold tailWord_2595954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23670555209327371622780729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63121480558206324327415277 23670555209327371622780729)
  ·
    refine ⟨17752916406995528717085547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23670555209327371622780729 17752916406995528717085547)
    ·
      refine ⟨26629374610493293075628321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17752916406995528717085547 26629374610493293075628321)
      ·
        refine ⟨19972030957869969806721241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26629374610493293075628321 19972030957869969806721241)
        ·
          refine ⟨14979023218402477355040931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19972030957869969806721241 14979023218402477355040931)
          ·
            refine ⟨22468534827603716032561397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14979023218402477355040931 22468534827603716032561397)
            ·
              refine ⟨2106425140087848378052631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22468534827603716032561397 2106425140087848378052631)
              ·
                refine ⟨3159637710131772567078947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106425140087848378052631 3159637710131772567078947)
                ·
                  refine ⟨4739456565197658850618421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159637710131772567078947 4739456565197658850618421)
                  ·
                    refine ⟨444324052987280517245477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4739456565197658850618421 444324052987280517245477)
                    ·
                      rfl

theorem cell23_2595954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_2595954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595954 prefixEnd_2595954 := by exact prefixLift 2595954
  have htrace : WordTrace (prefixWord ++ tailWord_2595954) baseStart_2595954 baseEnd_2595954 := by
    simpa [prefixWord, tailWord_2595954, baseEnd_2595954] using wordTrace_append hprefix tailTrace_2595954
  have hstable : (prefixWord ++ tailWord_2595954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595954).length < 2 ^ (prefixWord ++ tailWord_2595954).sum := by decide
  have hdescent : baseEnd_2595954 < baseStart_2595954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595977 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_2595977 : Nat := 118140960795 + 2595977 * 2 ^ 59
def prefixEnd_2595977 : Nat := 4983230072969 + 3 ^ 40 * 2595977 * 2
def baseEnd_2595977 : Nat := 1332983969016894961748825

theorem tailTrace_2595977 : CollatzResearch.WordTrace tailWord_2595977 prefixEnd_2595977 1332983969016894961748825 := by
  unfold tailWord_2595977
  simp only [CollatzResearch.WordTrace]
  refine ⟨94683059716226161419210185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63122039810817440946140123 94683059716226161419210185)
  ·
    refine ⟨71012294787169621064407639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94683059716226161419210185 71012294787169621064407639)
    ·
      refine ⟨106518442180754431596611459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71012294787169621064407639 106518442180754431596611459)
      ·
        refine ⟨159777663271131647394917189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106518442180754431596611459 159777663271131647394917189)
        ·
          refine ⟨29958311863337183886546973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159777663271131647394917189 29958311863337183886546973)
          ·
            refine ⟨11234366948751443957455115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29958311863337183886546973 11234366948751443957455115)
            ·
              refine ⟨16851550423127165936182673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11234366948751443957455115 16851550423127165936182673)
              ·
                refine ⟨12638662817345374452137005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16851550423127165936182673 12638662817345374452137005)
                ·
                  refine ⟨4739498556504515419551377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12638662817345374452137005 4739498556504515419551377)
                  ·
                    refine ⟨3554623917378386564663533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4739498556504515419551377 3554623917378386564663533)
                    ·
                      refine ⟨1332983969016894961748825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3554623917378386564663533 1332983969016894961748825)
                      ·
                        rfl

theorem cell23_2595977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_2595977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595977 prefixEnd_2595977 := by exact prefixLift 2595977
  have htrace : WordTrace (prefixWord ++ tailWord_2595977) baseStart_2595977 baseEnd_2595977 := by
    simpa [prefixWord, tailWord_2595977, baseEnd_2595977] using wordTrace_append hprefix tailTrace_2595977
  have hstable : (prefixWord ++ tailWord_2595977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595977).length < 2 ^ (prefixWord ++ tailWord_2595977).sum := by decide
  have hdescent : baseEnd_2595977 < baseStart_2595977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595991 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 3, 2, 2]
def baseStart_2595991 : Nat := 118140960795 + 2595991 * 2 ^ 59
def prefixEnd_2595991 : Nat := 4983230072969 + 3 ^ 40 * 2595991 * 2
def baseEnd_2595991 : Nat := 1332991157746057906973761

theorem tailTrace_2595991 : CollatzResearch.WordTrace tailWord_2595991 prefixEnd_2595991 1332991157746057906973761 := by
  unfold tailWord_2595991
  simp only [CollatzResearch.WordTrace]
  refine ⟨94683570338175441810219827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63122380225450294540146551 94683570338175441810219827)
  ·
    refine ⟨142025355507263162715329741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94683570338175441810219827 142025355507263162715329741)
    ·
      refine ⟨53259508315223686018248653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142025355507263162715329741 53259508315223686018248653)
      ·
        refine ⟨19972315618208882256843245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53259508315223686018248653 19972315618208882256843245)
        ·
          refine ⟨7489618356828330846316217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19972315618208882256843245 7489618356828330846316217)
          ·
            refine ⟨5617213767621248134737163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7489618356828330846316217 5617213767621248134737163)
            ·
              refine ⟨8425820651431872202105745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617213767621248134737163 8425820651431872202105745)
              ·
                refine ⟨6319365488573904151579309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8425820651431872202105745 6319365488573904151579309)
                ·
                  refine ⟨2369762058215214056842241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6319365488573904151579309 2369762058215214056842241)
                  ·
                    refine ⟨1777321543661410542631681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369762058215214056842241 1777321543661410542631681)
                    ·
                      refine ⟨1332991157746057906973761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777321543661410542631681 1332991157746057906973761)
                      ·
                        rfl

theorem cell23_2595991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_2595991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595991 prefixEnd_2595991 := by exact prefixLift 2595991
  have htrace : WordTrace (prefixWord ++ tailWord_2595991) baseStart_2595991 baseEnd_2595991 := by
    simpa [prefixWord, tailWord_2595991, baseEnd_2595991] using wordTrace_append hprefix tailTrace_2595991
  have hstable : (prefixWord ++ tailWord_2595991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595991).length < 2 ^ (prefixWord ++ tailWord_2595991).sum := by decide
  have hdescent : baseEnd_2595991 < baseStart_2595991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595994 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2595994 : Nat := 118140960795 + 2595994 * 2 ^ 59
def prefixEnd_2595994 : Nat := 4983230072969 + 3 ^ 40 * 2595994 * 2
def baseEnd_2595994 : Nat := 1332992698188021395236247

theorem tailTrace_2595994 : CollatzResearch.WordTrace tailWord_2595994 prefixEnd_2595994 1332992698188021395236247 := by
  unfold tailWord_2595994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23670919939291143330644759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63122453171443048881719357 23670919939291143330644759)
  ·
    refine ⟨35506379908936714995967139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23670919939291143330644759 35506379908936714995967139)
    ·
      refine ⟨53259569863405072493950709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35506379908936714995967139 53259569863405072493950709)
      ·
        refine ⟨4993084674694225546307879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53259569863405072493950709 4993084674694225546307879)
        ·
          refine ⟨7489627012041338319461819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993084674694225546307879 7489627012041338319461819)
          ·
            refine ⟨11234440518062007479192729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7489627012041338319461819 11234440518062007479192729)
            ·
              refine ⟨8425830388546505609394547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11234440518062007479192729 8425830388546505609394547)
              ·
                refine ⟨12638745582819758414091821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8425830388546505609394547 12638745582819758414091821)
                ·
                  refine ⟨4739529593557409405284433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12638745582819758414091821 4739529593557409405284433)
                  ·
                    refine ⟨3554647195168057053963325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4739529593557409405284433 3554647195168057053963325)
                    ·
                      refine ⟨1332992698188021395236247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3554647195168057053963325 1332992698188021395236247)
                      ·
                        rfl

theorem cell23_2595994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2595994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595994 prefixEnd_2595994 := by exact prefixLift 2595994
  have htrace : WordTrace (prefixWord ++ tailWord_2595994) baseStart_2595994 baseEnd_2595994 := by
    simpa [prefixWord, tailWord_2595994, baseEnd_2595994] using wordTrace_append hprefix tailTrace_2595994
  have hstable : (prefixWord ++ tailWord_2595994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595994).length < 2 ^ (prefixWord ++ tailWord_2595994).sum := by decide
  have hdescent : baseEnd_2595994 < baseStart_2595994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595997 : List Nat := [1, 4, 2, 1, 1, 2, 5, 7]
def baseStart_2595997 : Nat := 118140960795 + 2595997 * 2 ^ 59
def prefixEnd_2595997 : Nat := 4983230072969 + 3 ^ 40 * 2595997 * 2
def baseEnd_2595997 : Nat := 49370156986295736425879

theorem tailTrace_2595997 : CollatzResearch.WordTrace tailWord_2595997 prefixEnd_2595997 49370156986295736425879 := by
  unfold tailWord_2595997
  simp only [CollatzResearch.WordTrace]
  refine ⟨94683789176153704834938245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63122526117435803223292163 94683789176153704834938245)
  ·
    refine ⟨17753210470528819656550921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94683789176153704834938245 17753210470528819656550921)
    ·
      refine ⟨13314907852896614742413191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17753210470528819656550921 13314907852896614742413191)
      ·
        refine ⟨19972361779344922113619787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13314907852896614742413191 19972361779344922113619787)
        ·
          refine ⟨29958542669017383170429681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19972361779344922113619787 29958542669017383170429681)
          ·
            refine ⟨22468907001763037377822261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29958542669017383170429681 22468907001763037377822261)
            ·
              refine ⟨2106460031415284754170837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22468907001763037377822261 2106460031415284754170837)
              ·
                refine ⟨49370156986295736425879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2106460031415284754170837 49370156986295736425879)
                ·
                  rfl

theorem cell23_2595997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 7].length) (baseStart_2595997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595997 prefixEnd_2595997 := by exact prefixLift 2595997
  have htrace : WordTrace (prefixWord ++ tailWord_2595997) baseStart_2595997 baseEnd_2595997 := by
    simpa [prefixWord, tailWord_2595997, baseEnd_2595997] using wordTrace_append hprefix tailTrace_2595997
  have hstable : (prefixWord ++ tailWord_2595997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595997).length < 2 ^ (prefixWord ++ tailWord_2595997).sum := by decide
  have hdescent : baseEnd_2595997 < baseStart_2595997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596024 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_2596024 : Nat := 118140960795 + 2596024 * 2 ^ 59
def prefixEnd_2596024 : Nat := 4983230072969 + 3 ^ 40 * 2596024 * 2
def baseEnd_2596024 : Nat := 1333008102607656277861109

theorem tailTrace_2596024 : CollatzResearch.WordTrace tailWord_2596024 prefixEnd_2596024 1333008102607656277861109 := by
  unfold tailWord_2596024
  simp only [CollatzResearch.WordTrace]
  refine ⟨47342386973527944223085563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63123182631370592297447417 47342386973527944223085563)
  ·
    refine ⟨71013580460291916334628345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47342386973527944223085563 71013580460291916334628345)
    ·
      refine ⟨53260185345218937250971259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71013580460291916334628345 53260185345218937250971259)
      ·
        refine ⟨79890278017828405876456889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53260185345218937250971259 79890278017828405876456889)
        ·
          refine ⟨59917708513371304407342667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79890278017828405876456889 59917708513371304407342667)
          ·
            refine ⟨89876562770056956611014001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59917708513371304407342667 89876562770056956611014001)
            ·
              refine ⟨67407422077542717458260501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89876562770056956611014001 67407422077542717458260501)
              ·
                refine ⟨3159722909884814880855961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67407422077542717458260501 3159722909884814880855961)
                ·
                  refine ⟨2369792182413611160641971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159722909884814880855961 2369792182413611160641971)
                  ·
                    refine ⟨3554688273620416740962957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2369792182413611160641971 3554688273620416740962957)
                    ·
                      refine ⟨1333008102607656277861109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3554688273620416740962957 1333008102607656277861109)
                      ·
                        rfl

theorem cell23_2596024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_2596024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596024 prefixEnd_2596024 := by exact prefixLift 2596024
  have htrace : WordTrace (prefixWord ++ tailWord_2596024) baseStart_2596024 baseEnd_2596024 := by
    simpa [prefixWord, tailWord_2596024, baseEnd_2596024] using wordTrace_append hprefix tailTrace_2596024
  have hstable : (prefixWord ++ tailWord_2596024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596024).length < 2 ^ (prefixWord ++ tailWord_2596024).sum := by decide
  have hdescent : baseEnd_2596024 < baseStart_2596024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596038 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2596038 : Nat := 118140960795 + 2596038 * 2 ^ 59
def prefixEnd_2596038 : Nat := 4983230072969 + 3 ^ 40 * 2596038 * 2
def baseEnd_2596038 : Nat := 1333015291336819223086045

theorem tailTrace_2596038 : CollatzResearch.WordTrace tailWord_2596038 prefixEnd_2596038 1333015291336819223086045 := by
  unfold tailWord_2596038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958915142781411526161899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63123523046003445891453845 2958915142781411526161899)
  ·
    refine ⟨4438372714172117289242849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2958915142781411526161899 4438372714172117289242849)
    ·
      refine ⟨3328779535629087966932137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4438372714172117289242849 3328779535629087966932137)
      ·
        refine ⟨2496584651721815975199103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3328779535629087966932137 2496584651721815975199103)
        ·
          refine ⟨3744876977582723962798655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496584651721815975199103 3744876977582723962798655)
          ·
            refine ⟨5617315466374085944197983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744876977582723962798655 5617315466374085944197983)
            ·
              refine ⟨8425973199561128916296975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617315466374085944197983 8425973199561128916296975)
              ·
                refine ⟨12638959799341693374445463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8425973199561128916296975 12638959799341693374445463)
                ·
                  refine ⟨18958439699012540061668195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12638959799341693374445463 18958439699012540061668195)
                  ·
                    refine ⟨28437659548518810092502293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18958439699012540061668195 28437659548518810092502293)
                    ·
                      refine ⟨1333015291336819223086045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28437659548518810092502293 1333015291336819223086045)
                      ·
                        rfl

theorem cell23_2596038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2596038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596038 prefixEnd_2596038 := by exact prefixLift 2596038
  have htrace : WordTrace (prefixWord ++ tailWord_2596038) baseStart_2596038 baseEnd_2596038 := by
    simpa [prefixWord, tailWord_2596038, baseEnd_2596038] using wordTrace_append hprefix tailTrace_2596038
  have hstable : (prefixWord ++ tailWord_2596038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596038).length < 2 ^ (prefixWord ++ tailWord_2596038).sum := by decide
  have hdescent : baseEnd_2596038 < baseStart_2596038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596045 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2596045 : Nat := 118140960795 + 2596045 * 2 ^ 59
def prefixEnd_2596045 : Nat := 4983230072969 + 3 ^ 40 * 2596045 * 2
def baseEnd_2596045 : Nat := 1333018885701400695698513

theorem tailTrace_2596045 : CollatzResearch.WordTrace tailWord_2596045 prefixEnd_2596045 1333018885701400695698513 := by
  unfold tailWord_2596045
  simp only [CollatzResearch.WordTrace]
  refine ⟨94685539879979809032685589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63123693253319872688457059 94685539879979809032685589)
  ·
    refine ⟨4438384681874053548407137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94685539879979809032685589 4438384681874053548407137)
    ·
      refine ⟨3328788511405540161305353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4438384681874053548407137 3328788511405540161305353)
      ·
        refine ⟨2496591383554155120979015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3328788511405540161305353 2496591383554155120979015)
        ·
          refine ⟨3744887075331232681468523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496591383554155120979015 3744887075331232681468523)
          ·
            refine ⟨5617330612996849022202785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744887075331232681468523 5617330612996849022202785)
            ·
              refine ⟨4212997959747636766652089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617330612996849022202785 4212997959747636766652089)
              ·
                refine ⟨3159748469810727574989067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212997959747636766652089 3159748469810727574989067)
                ·
                  refine ⟨4739622704716091362483601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159748469810727574989067 4739622704716091362483601)
                  ·
                    refine ⟨3554717028537068521862701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4739622704716091362483601 3554717028537068521862701)
                    ·
                      refine ⟨1333018885701400695698513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3554717028537068521862701 1333018885701400695698513)
                      ·
                        rfl

theorem cell23_2596045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2596045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596045 prefixEnd_2596045 := by exact prefixLift 2596045
  have htrace : WordTrace (prefixWord ++ tailWord_2596045) baseStart_2596045 baseEnd_2596045 := by
    simpa [prefixWord, tailWord_2596045, baseEnd_2596045] using wordTrace_append hprefix tailTrace_2596045
  have hstable : (prefixWord ++ tailWord_2596045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596045).length < 2 ^ (prefixWord ++ tailWord_2596045).sum := by decide
  have hdescent : baseEnd_2596045 < baseStart_2596045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596081 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 2, 2, 2]
def baseStart_2596081 : Nat := 118140960795 + 2596081 * 2 ^ 59
def prefixEnd_2596081 : Nat := 4983230072969 + 3 ^ 40 * 2596081 * 2
def baseEnd_2596081 : Nat := 1333037371004962554848347

theorem tailTrace_2596081 : CollatzResearch.WordTrace tailWord_2596081 prefixEnd_2596081 1333037371004962554848347 := by
  unfold tailWord_2596081
  simp only [CollatzResearch.WordTrace]
  refine ⟨94686852907849387180996097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63124568605232924787330731 94686852907849387180996097)
  ·
    refine ⟨71015139680887040385747073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94686852907849387180996097 71015139680887040385747073)
    ·
      refine ⟨53261354760665280289310305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71015139680887040385747073 53261354760665280289310305)
      ·
        refine ⟨39946016070498960216982729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53261354760665280289310305 39946016070498960216982729)
        ·
          refine ⟨29959512052874220162737047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39946016070498960216982729 29959512052874220162737047)
          ·
            refine ⟨44939268079311330244105571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29959512052874220162737047 44939268079311330244105571)
            ·
              refine ⟨67408902118966995366158357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44939268079311330244105571 67408902118966995366158357)
              ·
                refine ⟨3159792286826577907788673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67408902118966995366158357 3159792286826577907788673)
                ·
                  refine ⟨2369844215119933430841505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159792286826577907788673 2369844215119933430841505)
                  ·
                    refine ⟨1777383161339950073131129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369844215119933430841505 1777383161339950073131129)
                    ·
                      refine ⟨1333037371004962554848347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777383161339950073131129 1333037371004962554848347)
                      ·
                        rfl

theorem cell23_2596081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_2596081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596081 prefixEnd_2596081 := by exact prefixLift 2596081
  have htrace : WordTrace (prefixWord ++ tailWord_2596081) baseStart_2596081 baseEnd_2596081 := by
    simpa [prefixWord, tailWord_2596081, baseEnd_2596081] using wordTrace_append hprefix tailTrace_2596081
  have hstable : (prefixWord ++ tailWord_2596081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596081).length < 2 ^ (prefixWord ++ tailWord_2596081).sum := by decide
  have hdescent : baseEnd_2596081 < baseStart_2596081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596137 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_2596137 : Nat := 118140960795 + 2596137 * 2 ^ 59
def prefixEnd_2596137 : Nat := 4983230072969 + 3 ^ 40 * 2596137 * 2
def baseEnd_2596137 : Nat := 1333066125921614335748089

theorem tailTrace_2596137 : CollatzResearch.WordTrace tailWord_2596137 prefixEnd_2596137 1333066125921614335748089 := by
  unfold tailWord_2596137
  simp only [CollatzResearch.WordTrace]
  refine ⟨94688895395646508745034665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63125930263764339163356443 94688895395646508745034665)
  ·
    refine ⟨71016671546734881558775999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94688895395646508745034665 71016671546734881558775999)
    ·
      refine ⟨106525007320102322338163999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71016671546734881558775999 106525007320102322338163999)
      ·
        refine ⟨159787510980153483507245999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106525007320102322338163999 159787510980153483507245999)
        ·
          refine ⟨239681266470230225260868999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159787510980153483507245999 239681266470230225260868999)
          ·
            refine ⟨359521899705345337891303499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239681266470230225260868999 359521899705345337891303499)
            ·
              refine ⟨539282849558018006836955249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359521899705345337891303499 539282849558018006836955249)
              ·
                refine ⟨404462137168513505127716437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539282849558018006836955249 404462137168513505127716437)
                ·
                  refine ⟨4739790669943517638215427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 404462137168513505127716437 4739790669943517638215427)
                  ·
                    refine ⟨7109686004915276457323141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4739790669943517638215427 7109686004915276457323141)
                    ·
                      refine ⟨1333066125921614335748089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7109686004915276457323141 1333066125921614335748089)
                      ·
                        rfl

theorem cell23_2596137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_2596137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596137 prefixEnd_2596137 := by exact prefixLift 2596137
  have htrace : WordTrace (prefixWord ++ tailWord_2596137) baseStart_2596137 baseEnd_2596137 := by
    simpa [prefixWord, tailWord_2596137, baseEnd_2596137] using wordTrace_append hprefix tailTrace_2596137
  have hstable : (prefixWord ++ tailWord_2596137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596137).length < 2 ^ (prefixWord ++ tailWord_2596137).sum := by decide
  have hdescent : baseEnd_2596137 < baseStart_2596137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596138 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_2596138 : Nat := 118140960795 + 2596138 * 2 ^ 59
def prefixEnd_2596138 : Nat := 4983230072969 + 3 ^ 40 * 2596138 * 2
def baseEnd_2596138 : Nat := 148118515489140981315065

theorem tailTrace_2596138 : CollatzResearch.WordTrace tailWord_2596138 prefixEnd_2596138 148118515489140981315065 := by
  unfold tailWord_2596138
  simp only [CollatzResearch.WordTrace]
  refine ⟨23672232967160721478955267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63125954579095257277214045 23672232967160721478955267)
  ·
    refine ⟨35508349450741082218432901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23672232967160721478955267 35508349450741082218432901)
    ·
      refine ⟨6657815522013952915956169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35508349450741082218432901 6657815522013952915956169)
      ·
        refine ⟨4993361641510464686967127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6657815522013952915956169 4993361641510464686967127)
        ·
          refine ⟨7490042462265697030450691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993361641510464686967127 7490042462265697030450691)
          ·
            refine ⟨11235063693398545545676037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7490042462265697030450691 11235063693398545545676037)
            ·
              refine ⟨2106574442512227289814257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11235063693398545545676037 2106574442512227289814257)
              ·
                refine ⟨1579930831884170467360693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106574442512227289814257 1579930831884170467360693)
                ·
                  refine ⟨148118515489140981315065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1579930831884170467360693 148118515489140981315065)
                  ·
                    rfl

theorem cell23_2596138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_2596138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596138 prefixEnd_2596138 := by exact prefixLift 2596138
  have htrace : WordTrace (prefixWord ++ tailWord_2596138) baseStart_2596138 baseEnd_2596138 := by
    simpa [prefixWord, tailWord_2596138, baseEnd_2596138] using wordTrace_append hprefix tailTrace_2596138
  have hstable : (prefixWord ++ tailWord_2596138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596138).length < 2 ^ (prefixWord ++ tailWord_2596138).sum := by decide
  have hdescent : baseEnd_2596138 < baseStart_2596138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596174 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2596174 : Nat := 118140960795 + 2596174 * 2 ^ 59
def prefixEnd_2596174 : Nat := 4983230072969 + 3 ^ 40 * 2596174 * 2
def baseEnd_2596174 : Nat := 1333085124705830690985419

theorem tailTrace_2596174 : CollatzResearch.WordTrace tailWord_2596174 prefixEnd_2596174 1333085124705830690985419 := by
  unfold tailWord_2596174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11836280612064058008016447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63126829931008309376087717 11836280612064058008016447)
  ·
    refine ⟨17754420918096087012024671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11836280612064058008016447 17754420918096087012024671)
    ·
      refine ⟨26631631377144130518037007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17754420918096087012024671 26631631377144130518037007)
      ·
        refine ⟨39947447065716195777055511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26631631377144130518037007 39947447065716195777055511)
        ·
          refine ⟨59921170598574293665583267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39947447065716195777055511 59921170598574293665583267)
          ·
            refine ⟨89881755897861440498374901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59921170598574293665583267 89881755897861440498374901)
            ·
              refine ⟨8426414615424510046722647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89881755897861440498374901 8426414615424510046722647)
              ·
                refine ⟨12639621923136765070083971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8426414615424510046722647 12639621923136765070083971)
                ·
                  refine ⟨18959432884705147605125957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12639621923136765070083971 18959432884705147605125957)
                  ·
                    refine ⟨3554893665882215175961117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18959432884705147605125957 3554893665882215175961117)
                    ·
                      refine ⟨1333085124705830690985419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3554893665882215175961117 1333085124705830690985419)
                      ·
                        rfl

theorem cell23_2596174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2596174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596174 prefixEnd_2596174 := by exact prefixLift 2596174
  have htrace : WordTrace (prefixWord ++ tailWord_2596174) baseStart_2596174 baseEnd_2596174 := by
    simpa [prefixWord, tailWord_2596174, baseEnd_2596174] using wordTrace_append hprefix tailTrace_2596174
  have hstable : (prefixWord ++ tailWord_2596174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596174).length < 2 ^ (prefixWord ++ tailWord_2596174).sum := by decide
  have hdescent : baseEnd_2596174 < baseStart_2596174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596177 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 8]
def baseStart_2596177 : Nat := 118140960795 + 2596177 * 2 ^ 59
def prefixEnd_2596177 : Nat := 4983230072969 + 3 ^ 40 * 2596177 * 2
def baseEnd_2596177 : Nat := 148120740571977131027545

theorem tailTrace_2596177 : CollatzResearch.WordTrace tailWord_2596177 prefixEnd_2596177 148120740571977131027545 := by
  unfold tailWord_2596177
  simp only [CollatzResearch.WordTrace]
  refine ⟨94690354315501595576490785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63126902877001063717660523 94690354315501595576490785)
  ·
    refine ⟨71017765736626196682368089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94690354315501595576490785 71017765736626196682368089)
    ·
      refine ⟨53263324302469647511776067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71017765736626196682368089 53263324302469647511776067)
      ·
        refine ⟨79894986453704471267664101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53263324302469647511776067 79894986453704471267664101)
        ·
          refine ⟨14980309960069588362687019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79894986453704471267664101 14980309960069588362687019)
          ·
            refine ⟨22470464940104382544030529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14980309960069588362687019 22470464940104382544030529)
            ·
              refine ⟨16852848705078286908022897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22470464940104382544030529 16852848705078286908022897)
              ·
                refine ⟨12639636528808715181017173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16852848705078286908022897 12639636528808715181017173)
                ·
                  refine ⟨148120740571977131027545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12639636528808715181017173 148120740571977131027545)
                  ·
                    rfl

theorem cell23_2596177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_2596177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596177 prefixEnd_2596177 := by exact prefixLift 2596177
  have htrace : WordTrace (prefixWord ++ tailWord_2596177) baseStart_2596177 baseEnd_2596177 := by
    simpa [prefixWord, tailWord_2596177, baseEnd_2596177] using wordTrace_append hprefix tailTrace_2596177
  have hstable : (prefixWord ++ tailWord_2596177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596177).length < 2 ^ (prefixWord ++ tailWord_2596177).sum := by decide
  have hdescent : baseEnd_2596177 < baseStart_2596177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596194 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_2596194 : Nat := 118140960795 + 2596194 * 2 ^ 59
def prefixEnd_2596194 : Nat := 4983230072969 + 3 ^ 40 * 2596194 * 2
def baseEnd_2596194 : Nat := 148121710479880068081703

theorem tailTrace_2596194 : CollatzResearch.WordTrace tailWord_2596194 prefixEnd_2596194 148121710479880068081703 := by
  unfold tailWord_2596194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23672743589110001869964909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63127316237626671653239757 23672743589110001869964909)
  ·
    refine ⟨8877278845916250701236841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23672743589110001869964909 8877278845916250701236841)
    ·
      refine ⟨6657959134437188025927631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8877278845916250701236841 6657959134437188025927631)
      ·
        refine ⟨9986938701655782038891447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6657959134437188025927631 9986938701655782038891447)
        ·
          refine ⟨14980408052483673058337171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9986938701655782038891447 14980408052483673058337171)
          ·
            refine ⟨22470612078725509587505757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14980408052483673058337171 22470612078725509587505757)
            ·
              refine ⟨8426479529522066095314659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22470612078725509587505757 8426479529522066095314659)
              ·
                refine ⟨12639719294283099142971989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8426479529522066095314659 12639719294283099142971989)
                ·
                  refine ⟨148121710479880068081703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12639719294283099142971989 148121710479880068081703)
                  ·
                    rfl

theorem cell23_2596194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_2596194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596194 prefixEnd_2596194 := by exact prefixLift 2596194
  have htrace : WordTrace (prefixWord ++ tailWord_2596194) baseStart_2596194 baseEnd_2596194 := by
    simpa [prefixWord, tailWord_2596194, baseEnd_2596194] using wordTrace_append hprefix tailTrace_2596194
  have hstable : (prefixWord ++ tailWord_2596194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596194).length < 2 ^ (prefixWord ++ tailWord_2596194).sum := by decide
  have hdescent : baseEnd_2596194 < baseStart_2596194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596197 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2596197 : Nat := 118140960795 + 2596197 * 2 ^ 59
def prefixEnd_2596197 : Nat := 4983230072969 + 3 ^ 40 * 2596197 * 2
def baseEnd_2596197 : Nat := 1333096934760884100997813

theorem tailTrace_2596197 : CollatzResearch.WordTrace tailWord_2596197 prefixEnd_2596197 1333096934760884100997813 := by
  unfold tailWord_2596197
  simp only [CollatzResearch.WordTrace]
  refine ⟨94691083775429138992218845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63127389183619425994812563 94691083775429138992218845)
  ·
    refine ⟨35509156415785927122082067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94691083775429138992218845 35509156415785927122082067)
    ·
      refine ⟨53263734623678890683123101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35509156415785927122082067 53263734623678890683123101)
      ·
        refine ⟨19973900483879584006171163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53263734623678890683123101 19973900483879584006171163)
        ·
          refine ⟨29960850725819376009256745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19973900483879584006171163 29960850725819376009256745)
          ·
            refine ⟨22470638044364532006942559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29960850725819376009256745 22470638044364532006942559)
            ·
              refine ⟨33705957066546798010413839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22470638044364532006942559 33705957066546798010413839)
              ·
                refine ⟨50558935599820197015620759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33705957066546798010413839 50558935599820197015620759)
                ·
                  refine ⟨75838403399730295523431139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50558935599820197015620759 75838403399730295523431139)
                  ·
                    refine ⟨113757605099595443285146709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75838403399730295523431139 113757605099595443285146709)
                    ·
                      refine ⟨1333096934760884100997813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 113757605099595443285146709 1333096934760884100997813)
                      ·
                        rfl

theorem cell23_2596197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2596197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596197 prefixEnd_2596197 := by exact prefixLift 2596197
  have htrace : WordTrace (prefixWord ++ tailWord_2596197) baseStart_2596197 baseEnd_2596197 := by
    simpa [prefixWord, tailWord_2596197, baseEnd_2596197] using wordTrace_append hprefix tailTrace_2596197
  have hstable : (prefixWord ++ tailWord_2596197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596197).length < 2 ^ (prefixWord ++ tailWord_2596197).sum := by decide
  have hdescent : baseEnd_2596197 < baseStart_2596197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596217 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2596217 : Nat := 118140960795 + 2596217 * 2 ^ 59
def prefixEnd_2596217 : Nat := 4983230072969 + 3 ^ 40 * 2596217 * 2
def baseEnd_2596217 : Nat := 1333107204373974022747721

theorem tailTrace_2596217 : CollatzResearch.WordTrace tailWord_2596217 prefixEnd_2596217 1333107204373974022747721 := by
  unfold tailWord_2596217
  simp only [CollatzResearch.WordTrace]
  refine ⟨94691813235356682407946905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63127875490237788271964603 94691813235356682407946905)
  ·
    refine ⟨71018859926517511805960179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94691813235356682407946905 71018859926517511805960179)
    ·
      refine ⟨106528289889776267708940269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71018859926517511805960179 106528289889776267708940269)
      ·
        refine ⟨39948108708666100390852601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106528289889776267708940269 39948108708666100390852601)
        ·
          refine ⟨29961081531499575293139451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39948108708666100390852601 29961081531499575293139451)
          ·
            refine ⟨44941622297249362939709177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29961081531499575293139451 44941622297249362939709177)
            ·
              refine ⟨33706216722937022204781883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44941622297249362939709177 33706216722937022204781883)
              ·
                refine ⟨50559325084405533307172825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33706216722937022204781883 50559325084405533307172825)
                ·
                  refine ⟨37919493813304149980379619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50559325084405533307172825 37919493813304149980379619)
                  ·
                    refine ⟨56879240719956224970569429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37919493813304149980379619 56879240719956224970569429)
                    ·
                      refine ⟨1333107204373974022747721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56879240719956224970569429 1333107204373974022747721)
                      ·
                        rfl

theorem cell23_2596217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2596217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596217 prefixEnd_2596217 := by exact prefixLift 2596217
  have htrace : WordTrace (prefixWord ++ tailWord_2596217) baseStart_2596217 baseEnd_2596217 := by
    simpa [prefixWord, tailWord_2596217, baseEnd_2596217] using wordTrace_append hprefix tailTrace_2596217
  have hstable : (prefixWord ++ tailWord_2596217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596217).length < 2 ^ (prefixWord ++ tailWord_2596217).sum := by decide
  have hdescent : baseEnd_2596217 < baseStart_2596217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596221 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_2596221 : Nat := 118140960795 + 2596221 * 2 ^ 59
def prefixEnd_2596221 : Nat := 4983230072969 + 3 ^ 40 * 2596221 * 2
def baseEnd_2596221 : Nat := 1333109258296592007097703

theorem tailTrace_2596221 : CollatzResearch.WordTrace tailWord_2596221 prefixEnd_2596221 1333109258296592007097703 := by
  unfold tailWord_2596221
  simp only [CollatzResearch.WordTrace]
  refine ⟨94691959127342191091092517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63127972751561460727395011 94691959127342191091092517)
  ·
    refine ⟨17754742336376660829579847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94691959127342191091092517 17754742336376660829579847)
    ·
      refine ⟨26632113504564991244369771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17754742336376660829579847 26632113504564991244369771)
      ·
        refine ⟨39948170256847486866554657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26632113504564991244369771 39948170256847486866554657)
        ·
          refine ⟨29961127692635615149915993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39948170256847486866554657 29961127692635615149915993)
          ·
            refine ⟨22470845769476711362436995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29961127692635615149915993 22470845769476711362436995)
            ·
              refine ⟨33706268654215067043655493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22470845769476711362436995 33706268654215067043655493)
              ·
                refine ⟨6319925372665325070685405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33706268654215067043655493 6319925372665325070685405)
                ·
                  refine ⟨2369972014749496901507027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6319925372665325070685405 2369972014749496901507027)
                  ·
                    refine ⟨3554958022124245352260541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2369972014749496901507027 3554958022124245352260541)
                    ·
                      refine ⟨1333109258296592007097703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3554958022124245352260541 1333109258296592007097703)
                      ·
                        rfl

theorem cell23_2596221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_2596221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596221 prefixEnd_2596221 := by exact prefixLift 2596221
  have htrace : WordTrace (prefixWord ++ tailWord_2596221) baseStart_2596221 baseEnd_2596221 := by
    simpa [prefixWord, tailWord_2596221, baseEnd_2596221] using wordTrace_append hprefix tailTrace_2596221
  have hstable : (prefixWord ++ tailWord_2596221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596221).length < 2 ^ (prefixWord ++ tailWord_2596221).sum := by decide
  have hdescent : baseEnd_2596221 < baseStart_2596221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596231 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_2596231 : Nat := 118140960795 + 2596231 * 2 ^ 59
def prefixEnd_2596231 : Nat := 4983230072969 + 3 ^ 40 * 2596231 * 2
def baseEnd_2596231 : Nat := 1333114393103136967972657

theorem tailTrace_2596231 : CollatzResearch.WordTrace tailWord_2596231 prefixEnd_2596231 1333114393103136967972657 := by
  unfold tailWord_2596231
  simp only [CollatzResearch.WordTrace]
  refine ⟨94692323857305962798956547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63128215904870641865971031 94692323857305962798956547)
  ·
    refine ⟨142038485785958944198434821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94692323857305962798956547 142038485785958944198434821)
    ·
      refine ⟨26632216084867302037206529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142038485785958944198434821 26632216084867302037206529)
      ·
        refine ⟨19974162063650476527904897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26632216084867302037206529 19974162063650476527904897)
        ·
          refine ⟨14980621547737857395928673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19974162063650476527904897 14980621547737857395928673)
          ·
            refine ⟨11235466160803393046946505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14980621547737857395928673 11235466160803393046946505)
            ·
              refine ⟨8426599620602544785209879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11235466160803393046946505 8426599620602544785209879)
              ·
                refine ⟨12639899430903817177814819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8426599620602544785209879 12639899430903817177814819)
                ·
                  refine ⟨18959849146355725766722229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12639899430903817177814819 18959849146355725766722229)
                  ·
                    refine ⟨1777485857470849290630209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18959849146355725766722229 1777485857470849290630209)
                    ·
                      refine ⟨1333114393103136967972657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777485857470849290630209 1333114393103136967972657)
                      ·
                        rfl

theorem cell23_2596231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_2596231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596231 prefixEnd_2596231 := by exact prefixLift 2596231
  have htrace : WordTrace (prefixWord ++ tailWord_2596231) baseStart_2596231 baseEnd_2596231 := by
    simpa [prefixWord, tailWord_2596231, baseEnd_2596231] using wordTrace_append hprefix tailTrace_2596231
  have hstable : (prefixWord ++ tailWord_2596231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596231).length < 2 ^ (prefixWord ++ tailWord_2596231).sum := by decide
  have hdescent : baseEnd_2596231 < baseStart_2596231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596295 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_2596295 : Nat := 118140960795 + 2596295 * 2 ^ 59
def prefixEnd_2596295 : Nat := 4983230072969 + 3 ^ 40 * 2596295 * 2
def baseEnd_2596295 : Nat := 1333147255865024717572363

theorem tailTrace_2596295 : CollatzResearch.WordTrace tailWord_2596295 prefixEnd_2596295 1333147255865024717572363 := by
  unfold tailWord_2596295
  simp only [CollatzResearch.WordTrace]
  refine ⟨94694658129074101729286339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63129772086049401152857559 94694658129074101729286339)
  ·
    refine ⟨142041987193611152593929509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94694658129074101729286339 142041987193611152593929509)
    ·
      refine ⟨26632872598802091111361783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142041987193611152593929509 26632872598802091111361783)
      ·
        refine ⟨39949308898203136667042675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26632872598802091111361783 39949308898203136667042675)
        ·
          refine ⟨59923963347304705000564013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39949308898203136667042675 59923963347304705000564013)
          ·
            refine ⟨22471486255239264375211505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59923963347304705000564013 22471486255239264375211505)
            ·
              refine ⟨16853614691429448281408629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22471486255239264375211505 16853614691429448281408629)
              ·
                refine ⟨1580026377321510776382059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16853614691429448281408629 1580026377321510776382059)
                ·
                  refine ⟨2370039565982266164573089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580026377321510776382059 2370039565982266164573089)
                  ·
                    refine ⟨1777529674486699623429817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2370039565982266164573089 1777529674486699623429817)
                    ·
                      refine ⟨1333147255865024717572363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777529674486699623429817 1333147255865024717572363)
                      ·
                        rfl

theorem cell23_2596295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_2596295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596295 prefixEnd_2596295 := by exact prefixLift 2596295
  have htrace : WordTrace (prefixWord ++ tailWord_2596295) baseStart_2596295 baseEnd_2596295 := by
    simpa [prefixWord, tailWord_2596295, baseEnd_2596295] using wordTrace_append hprefix tailTrace_2596295
  have hstable : (prefixWord ++ tailWord_2596295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596295).length < 2 ^ (prefixWord ++ tailWord_2596295).sum := by decide
  have hdescent : baseEnd_2596295 < baseStart_2596295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596311 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_2596311 : Nat := 118140960795 + 2596311 * 2 ^ 59
def prefixEnd_2596311 : Nat := 4983230072969 + 3 ^ 40 * 2596311 * 2
def baseEnd_2596311 : Nat := 1333155471555496654972289

theorem tailTrace_2596311 : CollatzResearch.WordTrace tailWord_2596311 prefixEnd_2596311 1333155471555496654972289 := by
  unfold tailWord_2596311
  simp only [CollatzResearch.WordTrace]
  refine ⟨94695241697016136461868787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63130161131344090974579191 94695241697016136461868787)
  ·
    refine ⟨142042862545524204692803181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94695241697016136461868787 142042862545524204692803181)
    ·
      refine ⟨53266073454571576759801193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142042862545524204692803181 53266073454571576759801193)
      ·
        refine ⟨39949555090928682569850895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53266073454571576759801193 39949555090928682569850895)
        ·
          refine ⟨59924332636393023854776343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39949555090928682569850895 59924332636393023854776343)
          ·
            refine ⟨89886498954589535782164515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59924332636393023854776343 89886498954589535782164515)
            ·
              refine ⟨134829748431884303673246773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89886498954589535782164515 134829748431884303673246773)
              ·
                refine ⟨12640288915489153469366885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134829748431884303673246773 12640288915489153469366885)
                ·
                  refine ⟨2370054171654216275506291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12640288915489153469366885 2370054171654216275506291)
                  ·
                    refine ⟨3555081257481324413259437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2370054171654216275506291 3555081257481324413259437)
                    ·
                      refine ⟨1333155471555496654972289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3555081257481324413259437 1333155471555496654972289)
                      ·
                        rfl

theorem cell23_2596311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_2596311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596311 prefixEnd_2596311 := by exact prefixLift 2596311
  have htrace : WordTrace (prefixWord ++ tailWord_2596311) baseStart_2596311 baseEnd_2596311 := by
    simpa [prefixWord, tailWord_2596311, baseEnd_2596311] using wordTrace_append hprefix tailTrace_2596311
  have hstable : (prefixWord ++ tailWord_2596311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596311).length < 2 ^ (prefixWord ++ tailWord_2596311).sum := by decide
  have hdescent : baseEnd_2596311 < baseStart_2596311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596312 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 1, 2, 2]
def baseStart_2596312 : Nat := 118140960795 + 2596312 * 2 ^ 59
def prefixEnd_2596312 : Nat := 4983230072969 + 3 ^ 40 * 2596312 * 2
def baseEnd_2596312 : Nat := 1333155985036151151059785

theorem tailTrace_2596312 : CollatzResearch.WordTrace tailWord_2596312 prefixEnd_2596312 1333155985036151151059785 := by
  unfold tailWord_2596312
  simp only [CollatzResearch.WordTrace]
  refine ⟨47347639085006256816327595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63130185446675009088436793 47347639085006256816327595)
  ·
    refine ⟨71021458627509385224491393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47347639085006256816327595 71021458627509385224491393)
    ·
      refine ⟨53266093970632038918368545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71021458627509385224491393 53266093970632038918368545)
      ·
        refine ⟨39949570477974029188776409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53266093970632038918368545 39949570477974029188776409)
        ·
          refine ⟨29962177858480521891582307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39949570477974029188776409 29962177858480521891582307)
          ·
            refine ⟨44943266787720782837373461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29962177858480521891582307 44943266787720782837373461)
            ·
              refine ⟨2106715630674411695501881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44943266787720782837373461 2106715630674411695501881)
              ·
                refine ⟨1580036723005808771626411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106715630674411695501881 1580036723005808771626411)
                ·
                  refine ⟨2370055084508713157439617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580036723005808771626411 2370055084508713157439617)
                  ·
                    refine ⟨1777541313381534868079713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2370055084508713157439617 1777541313381534868079713)
                    ·
                      refine ⟨1333155985036151151059785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777541313381534868079713 1333155985036151151059785)
                      ·
                        rfl

theorem cell23_2596312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_2596312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596312 prefixEnd_2596312 := by exact prefixLift 2596312
  have htrace : WordTrace (prefixWord ++ tailWord_2596312) baseStart_2596312 baseEnd_2596312 := by
    simpa [prefixWord, tailWord_2596312, baseEnd_2596312] using wordTrace_append hprefix tailTrace_2596312
  have hstable : (prefixWord ++ tailWord_2596312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596312).length < 2 ^ (prefixWord ++ tailWord_2596312).sum := by decide
  have hdescent : baseEnd_2596312 < baseStart_2596312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596314 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_2596314 : Nat := 118140960795 + 2596314 * 2 ^ 59
def prefixEnd_2596314 : Nat := 4983230072969 + 3 ^ 40 * 2596314 * 2
def baseEnd_2596314 : Nat := 444385670665820047744925

theorem tailTrace_2596314 : CollatzResearch.WordTrace tailWord_2596314 prefixEnd_2596314 444385670665820047744925 := by
  unfold tailWord_2596314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23673837779001316993556999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63130234077336845316151997 23673837779001316993556999)
  ·
    refine ⟨35510756668501975490335499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23673837779001316993556999 35510756668501975490335499)
    ·
      refine ⟨53266135002752963235503249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35510756668501975490335499 53266135002752963235503249)
      ·
        refine ⟨39949601252064722426627437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53266135002752963235503249 39949601252064722426627437)
        ·
          refine ⟨14981100469524270909985289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39949601252064722426627437 14981100469524270909985289)
          ·
            refine ⟨11235825352143203182488967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14981100469524270909985289 11235825352143203182488967)
            ·
              refine ⟨16853738028214804773733451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11235825352143203182488967 16853738028214804773733451)
              ·
                refine ⟨25280607042322207160600177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16853738028214804773733451 25280607042322207160600177)
                ·
                  refine ⟨18960455281741655370450133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25280607042322207160600177 18960455281741655370450133)
                  ·
                    refine ⟨444385670665820047744925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18960455281741655370450133 444385670665820047744925)
                    ·
                      rfl

theorem cell23_2596314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_2596314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596314 prefixEnd_2596314 := by exact prefixLift 2596314
  have htrace : WordTrace (prefixWord ++ tailWord_2596314) baseStart_2596314 baseEnd_2596314 := by
    simpa [prefixWord, tailWord_2596314, baseEnd_2596314] using wordTrace_append hprefix tailTrace_2596314
  have hstable : (prefixWord ++ tailWord_2596314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596314).length < 2 ^ (prefixWord ++ tailWord_2596314).sum := by decide
  have hdescent : baseEnd_2596314 < baseStart_2596314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596328 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2596328 : Nat := 118140960795 + 2596328 * 2 ^ 59
def prefixEnd_2596328 : Nat := 4983230072969 + 3 ^ 40 * 2596328 * 2
def baseEnd_2596328 : Nat := 1333164200726623088459711

theorem tailTrace_2596328 : CollatzResearch.WordTrace tailWord_2596328 prefixEnd_2596328 1333164200726623088459711 := by
  unfold tailWord_2596328
  simp only [CollatzResearch.WordTrace]
  refine ⟨47347930868977274182618819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63130574491969698910158425 47347930868977274182618819)
  ·
    refine ⟨71021896303465911273928229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47347930868977274182618819 71021896303465911273928229)
    ·
      refine ⟨13316605556899858363861543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71021896303465911273928229 13316605556899858363861543)
      ·
        refine ⟨19974908335349787545792315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13316605556899858363861543 19974908335349787545792315)
        ·
          refine ⟨29962362503024681318688473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19974908335349787545792315 29962362503024681318688473)
          ·
            refine ⟨22471771877268510989016355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29962362503024681318688473 22471771877268510989016355)
            ·
              refine ⟨33707657815902766483524533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22471771877268510989016355 33707657815902766483524533)
              ·
                refine ⟨3160092920240884357830425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33707657815902766483524533 3160092920240884357830425)
                ·
                  refine ⟨2370069690180663268372819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3160092920240884357830425 2370069690180663268372819)
                  ·
                    refine ⟨3555104535270994902559229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2370069690180663268372819 3555104535270994902559229)
                    ·
                      refine ⟨1333164200726623088459711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3555104535270994902559229 1333164200726623088459711)
                      ·
                        rfl

theorem cell23_2596328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2596328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596328 prefixEnd_2596328 := by exact prefixLift 2596328
  have htrace : WordTrace (prefixWord ++ tailWord_2596328) baseStart_2596328 baseEnd_2596328 := by
    simpa [prefixWord, tailWord_2596328, baseEnd_2596328] using wordTrace_append hprefix tailTrace_2596328
  have hstable : (prefixWord ++ tailWord_2596328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596328).length < 2 ^ (prefixWord ++ tailWord_2596328).sum := by decide
  have hdescent : baseEnd_2596328 < baseStart_2596328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596351 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 3, 4, 2]
def baseStart_2596351 : Nat := 118140960795 + 2596351 * 2 ^ 59
def prefixEnd_2596351 : Nat := 4983230072969 + 3 ^ 40 * 2596351 * 2
def baseEnd_2596351 : Nat := 1333176010781676498472105

theorem tailTrace_2596351 : CollatzResearch.WordTrace tailWord_2596351 prefixEnd_2596351 1333176010781676498472105 := by
  unfold tailWord_2596351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94696700616871223293324907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63131133744580815528883271 94696700616871223293324907)
  ·
    refine ⟨142045050925306834939987361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94696700616871223293324907 142045050925306834939987361)
    ·
      refine ⟨106533788193980126204990521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142045050925306834939987361 106533788193980126204990521)
      ·
        refine ⟨79900341145485094653742891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106533788193980126204990521 79900341145485094653742891)
        ·
          refine ⟨119850511718227641980614337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79900341145485094653742891 119850511718227641980614337)
          ·
            refine ⟨89887883788670731485460753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119850511718227641980614337 89887883788670731485460753)
            ·
              refine ⟨67415912841503048614095565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89887883788670731485460753 67415912841503048614095565)
              ·
                refine ⟨25280967315563643230285837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67415912841503048614095565 25280967315563643230285837)
                ·
                  refine ⟨9480362743336366211357189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25280967315563643230285837 9480362743336366211357189)
                  ·
                    refine ⟨1777568014375568664629473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9480362743336366211357189 1777568014375568664629473)
                    ·
                      refine ⟨1333176010781676498472105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777568014375568664629473 1333176010781676498472105)
                      ·
                        rfl

theorem cell23_2596351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_2596351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596351 prefixEnd_2596351 := by exact prefixLift 2596351
  have htrace : WordTrace (prefixWord ++ tailWord_2596351) baseStart_2596351 baseEnd_2596351 := by
    simpa [prefixWord, tailWord_2596351, baseEnd_2596351] using wordTrace_append hprefix tailTrace_2596351
  have hstable : (prefixWord ++ tailWord_2596351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596351).length < 2 ^ (prefixWord ++ tailWord_2596351).sum := by decide
  have hdescent : baseEnd_2596351 < baseStart_2596351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596381 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2596381 : Nat := 118140960795 + 2596381 * 2 ^ 59
def prefixEnd_2596381 : Nat := 4983230072969 + 3 ^ 40 * 2596381 * 2
def baseEnd_2596381 : Nat := 1333191415201311381096967

theorem tailTrace_2596381 : CollatzResearch.WordTrace tailWord_2596381 prefixEnd_2596381 1333191415201311381096967 := by
  unfold tailWord_2596381
  simp only [CollatzResearch.WordTrace]
  refine ⟨94697794806762538416916997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63131863204508358944611331 94697794806762538416916997)
  ·
    refine ⟨17755836526267975953171937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94697794806762538416916997 17755836526267975953171937)
    ·
      refine ⟨13316877394700981964878953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17755836526267975953171937 13316877394700981964878953)
      ·
        refine ⟨9987658046025736473659215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13316877394700981964878953 9987658046025736473659215)
        ·
          refine ⟨14981487069038604710488823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987658046025736473659215 14981487069038604710488823)
          ·
            refine ⟨22472230603557907065733235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14981487069038604710488823 22472230603557907065733235)
            ·
              refine ⟨33708345905336860598599853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22472230603557907065733235 33708345905336860598599853)
              ·
                refine ⟨12640629714501322724474945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33708345905336860598599853 12640629714501322724474945)
                ·
                  refine ⟨9480472285875992043356209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12640629714501322724474945 9480472285875992043356209)
                  ·
                    refine ⟨7110354214406994032517157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9480472285875992043356209 7110354214406994032517157)
                    ·
                      refine ⟨1333191415201311381096967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7110354214406994032517157 1333191415201311381096967)
                      ·
                        rfl

theorem cell23_2596381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2596381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596381 prefixEnd_2596381 := by exact prefixLift 2596381
  have htrace : WordTrace (prefixWord ++ tailWord_2596381) baseStart_2596381 baseEnd_2596381 := by
    simpa [prefixWord, tailWord_2596381, baseEnd_2596381] using wordTrace_append hprefix tailTrace_2596381
  have hstable : (prefixWord ++ tailWord_2596381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596381).length < 2 ^ (prefixWord ++ tailWord_2596381).sum := by decide
  have hdescent : baseEnd_2596381 < baseStart_2596381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596385 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_2596385 : Nat := 118140960795 + 2596385 * 2 ^ 59
def prefixEnd_2596385 : Nat := 4983230072969 + 3 ^ 40 * 2596385 * 2
def baseEnd_2596385 : Nat := 1333193469123929365446949

theorem tailTrace_2596385 : CollatzResearch.WordTrace tailWord_2596385 prefixEnd_2596385 1333193469123929365446949 := by
  unfold tailWord_2596385
  simp only [CollatzResearch.WordTrace]
  refine ⟨94697940698748047100062609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63131960465832031400041739 94697940698748047100062609)
  ·
    refine ⟨71023455524061035325046957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94697940698748047100062609 71023455524061035325046957)
    ·
      refine ⟨26633795821522888246892609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71023455524061035325046957 26633795821522888246892609)
      ·
        refine ⟨19975346866142166185169457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26633795821522888246892609 19975346866142166185169457)
        ·
          refine ⟨14981510149606624638877093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19975346866142166185169457 14981510149606624638877093)
          ·
            refine ⟨2809033153051242119789455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14981510149606624638877093 2809033153051242119789455)
            ·
              refine ⟨4213549729576863179684183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809033153051242119789455 4213549729576863179684183)
              ·
                refine ⟨6320324594365294769526275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4213549729576863179684183 6320324594365294769526275)
                ·
                  refine ⟨9480486891547942154289413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6320324594365294769526275 9480486891547942154289413)
                  ·
                    refine ⟨1777591292165239153929265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9480486891547942154289413 1777591292165239153929265)
                    ·
                      refine ⟨1333193469123929365446949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777591292165239153929265 1333193469123929365446949)
                      ·
                        rfl

theorem cell23_2596385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_2596385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596385 prefixEnd_2596385 := by exact prefixLift 2596385
  have htrace : WordTrace (prefixWord ++ tailWord_2596385) baseStart_2596385 baseEnd_2596385 := by
    simpa [prefixWord, tailWord_2596385, baseEnd_2596385] using wordTrace_append hprefix tailTrace_2596385
  have hstable : (prefixWord ++ tailWord_2596385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596385).length < 2 ^ (prefixWord ++ tailWord_2596385).sum := by decide
  have hdescent : baseEnd_2596385 < baseStart_2596385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596408 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 5]
def baseStart_2596408 : Nat := 118140960795 + 2596408 * 2 ^ 59
def prefixEnd_2596408 : Nat := 4983230072969 + 3 ^ 40 * 2596408 * 2
def baseEnd_2596408 : Nat := 148133919908775863939927

theorem tailTrace_2596408 : CollatzResearch.WordTrace tailWord_2596408 prefixEnd_2596408 148133919908775863939927 := by
  unfold tailWord_2596408
  simp only [CollatzResearch.WordTrace]
  refine ⟨47349389788832361014074939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63132519718443148018766585 47349389788832361014074939)
  ·
    refine ⟨71024084683248541521112409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47349389788832361014074939 71024084683248541521112409)
    ·
      refine ⟨53268063512436406140834307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71024084683248541521112409 53268063512436406140834307)
      ·
        refine ⟨79902095268654609211251461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53268063512436406140834307 79902095268654609211251461)
        ·
          refine ⟨14981642862872739227109649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79902095268654609211251461 14981642862872739227109649)
          ·
            refine ⟨11236232147154554420332237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14981642862872739227109649 11236232147154554420332237)
            ·
              refine ⟨4213587055182957907624589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11236232147154554420332237 4213587055182957907624589)
              ·
                refine ⟨1580095145693609215359221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4213587055182957907624589 1580095145693609215359221)
                ·
                  refine ⟨148133919908775863939927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580095145693609215359221 148133919908775863939927)
                  ·
                    rfl

theorem cell23_2596408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 5].length) (baseStart_2596408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596408 prefixEnd_2596408 := by exact prefixLift 2596408
  have htrace : WordTrace (prefixWord ++ tailWord_2596408) baseStart_2596408 baseEnd_2596408 := by
    simpa [prefixWord, tailWord_2596408, baseEnd_2596408] using wordTrace_append hprefix tailTrace_2596408
  have hstable : (prefixWord ++ tailWord_2596408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596408).length < 2 ^ (prefixWord ++ tailWord_2596408).sum := by decide
  have hdescent : baseEnd_2596408 < baseStart_2596408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596421 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_2596421 : Nat := 118140960795 + 2596421 * 2 ^ 59
def prefixEnd_2596421 : Nat := 4983230072969 + 3 ^ 40 * 2596421 * 2
def baseEnd_2596421 : Nat := 444403984809163741532261

theorem tailTrace_2596421 : CollatzResearch.WordTrace tailWord_2596421 prefixEnd_2596421 444403984809163741532261 := by
  unfold tailWord_2596421
  simp only [CollatzResearch.WordTrace]
  refine ⟨94699253726617625248373117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63132835817745083498915411 94699253726617625248373117)
  ·
    refine ⟨35512220147481609468139919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94699253726617625248373117 35512220147481609468139919)
    ·
      refine ⟨53268330221222414202209879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35512220147481609468139919 53268330221222414202209879)
      ·
        refine ⟨79902495331833621303314819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53268330221222414202209879 79902495331833621303314819)
        ·
          refine ⟨119853742997750431954972229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79902495331833621303314819 119853742997750431954972229)
          ·
            refine ⟨22472576812078205991557293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119853742997750431954972229 22472576812078205991557293)
            ·
              refine ⟨8427216304529327246833985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22472576812078205991557293 8427216304529327246833985)
              ·
                refine ⟨6320412228396995435125489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8427216304529327246833985 6320412228396995435125489)
                ·
                  refine ⟨4740309171297746576344117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6320412228396995435125489 4740309171297746576344117)
                  ·
                    refine ⟨444403984809163741532261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4740309171297746576344117 444403984809163741532261)
                    ·
                      rfl

theorem cell23_2596421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_2596421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596421 prefixEnd_2596421 := by exact prefixLift 2596421
  have htrace : WordTrace (prefixWord ++ tailWord_2596421) baseStart_2596421 baseEnd_2596421 := by
    simpa [prefixWord, tailWord_2596421, baseEnd_2596421] using wordTrace_append hprefix tailTrace_2596421
  have hstable : (prefixWord ++ tailWord_2596421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596421).length < 2 ^ (prefixWord ++ tailWord_2596421).sum := by decide
  have hdescent : baseEnd_2596421 < baseStart_2596421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596424 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2596424 : Nat := 118140960795 + 2596424 * 2 ^ 59
def prefixEnd_2596424 : Nat := 4983230072969 + 3 ^ 40 * 2596424 * 2
def baseEnd_2596424 : Nat := 1333213494869454712859269

theorem tailTrace_2596424 : CollatzResearch.WordTrace tailWord_2596424 prefixEnd_2596424 1333213494869454712859269 := by
  unfold tailWord_2596424
  simp only [CollatzResearch.WordTrace]
  refine ⟨47349681572803378380366163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63132908763737837840488217 47349681572803378380366163)
  ·
    refine ⟨71024522359205067570549245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47349681572803378380366163 71024522359205067570549245)
    ·
      refine ⟨26634195884701900338955967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71024522359205067570549245 26634195884701900338955967)
      ·
        refine ⟨39951293827052850508433951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26634195884701900338955967 39951293827052850508433951)
        ·
          refine ⟨59926940740579275762650927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39951293827052850508433951 59926940740579275762650927)
          ·
            refine ⟨89890411110868913643976391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59926940740579275762650927 89890411110868913643976391)
            ·
              refine ⟨134835616666303370465964587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89890411110868913643976391 134835616666303370465964587)
              ·
                refine ⟨202253424999455055698946881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134835616666303370465964587 202253424999455055698946881)
                ·
                  refine ⟨151690068749591291774210161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202253424999455055698946881 151690068749591291774210161)
                  ·
                    refine ⟨113767551562193468830657621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151690068749591291774210161 113767551562193468830657621)
                    ·
                      refine ⟨1333213494869454712859269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 113767551562193468830657621 1333213494869454712859269)
                      ·
                        rfl

theorem cell23_2596424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2596424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596424 prefixEnd_2596424 := by exact prefixLift 2596424
  have htrace : WordTrace (prefixWord ++ tailWord_2596424) baseStart_2596424 baseEnd_2596424 := by
    simpa [prefixWord, tailWord_2596424, baseEnd_2596424] using wordTrace_append hprefix tailTrace_2596424
  have hstable : (prefixWord ++ tailWord_2596424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596424).length < 2 ^ (prefixWord ++ tailWord_2596424).sum := by decide
  have hdescent : baseEnd_2596424 < baseStart_2596424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596458 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2596458 : Nat := 118140960795 + 2596458 * 2 ^ 59
def prefixEnd_2596458 : Nat := 4983230072969 + 3 ^ 40 * 2596458 * 2
def baseEnd_2596458 : Nat := 1333230953211707579834113

theorem tailTrace_2596458 : CollatzResearch.WordTrace tailWord_2596458 prefixEnd_2596458 1333230953211707579834113 := by
  unfold tailWord_2596458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23675150806870895141867507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63133735484989053711646685 23675150806870895141867507)
  ·
    refine ⟨35512726210306342712801261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23675150806870895141867507 35512726210306342712801261)
    ·
      refine ⟨13317272328864878517300473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35512726210306342712801261 13317272328864878517300473)
      ·
        refine ⟨9987954246648658887975355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13317272328864878517300473 9987954246648658887975355)
        ·
          refine ⟨14981931369972988331963033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987954246648658887975355 14981931369972988331963033)
          ·
            refine ⟨11236448527479741248972275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14981931369972988331963033 11236448527479741248972275)
            ·
              refine ⟨16854672791219611873458413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11236448527479741248972275 16854672791219611873458413)
              ·
                refine ⟨6320502296707354452546905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16854672791219611873458413 6320502296707354452546905)
                ·
                  refine ⟨4740376722530515839410179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6320502296707354452546905 4740376722530515839410179)
                  ·
                    refine ⟨7110565083795773759115269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4740376722530515839410179 7110565083795773759115269)
                    ·
                      refine ⟨1333230953211707579834113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7110565083795773759115269 1333230953211707579834113)
                      ·
                        rfl

theorem cell23_2596458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2596458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596458 prefixEnd_2596458 := by exact prefixLift 2596458
  have htrace : WordTrace (prefixWord ++ tailWord_2596458) baseStart_2596458 baseEnd_2596458 := by
    simpa [prefixWord, tailWord_2596458, baseEnd_2596458] using wordTrace_append hprefix tailTrace_2596458
  have hstable : (prefixWord ++ tailWord_2596458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596458).length < 2 ^ (prefixWord ++ tailWord_2596458).sum := by decide
  have hdescent : baseEnd_2596458 < baseStart_2596458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596485 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_2596485 : Nat := 118140960795 + 2596485 * 2 ^ 59
def prefixEnd_2596485 : Nat := 4983230072969 + 3 ^ 40 * 2596485 * 2
def baseEnd_2596485 : Nat := 444414939063126324732163

theorem tailTrace_2596485 : CollatzResearch.WordTrace tailWord_2596485 prefixEnd_2596485 444414939063126324732163 := by
  unfold tailWord_2596485
  simp only [CollatzResearch.WordTrace]
  refine ⟨94701587998385764178702909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63134391998923842785801939 94701587998385764178702909)
  ·
    refine ⟨35513095499394661567013591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94701587998385764178702909 35513095499394661567013591)
    ·
      refine ⟨53269643249091992350520387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35513095499394661567013591 53269643249091992350520387)
      ·
        refine ⟨79904464873637988525780581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53269643249091992350520387 79904464873637988525780581)
        ·
          refine ⟨14982087163807122848583859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79904464873637988525780581 14982087163807122848583859)
          ·
            refine ⟨22473130745710684272875789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14982087163807122848583859 22473130745710684272875789)
            ·
              refine ⟨8427424029641506602328421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22473130745710684272875789 8427424029641506602328421)
              ·
                refine ⟨1580142005557782487936579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8427424029641506602328421 1580142005557782487936579)
                ·
                  refine ⟨2370213008336673731904869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580142005557782487936579 2370213008336673731904869)
                  ·
                    refine ⟨444414939063126324732163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2370213008336673731904869 444414939063126324732163)
                    ·
                      rfl

theorem cell23_2596485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_2596485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596485 prefixEnd_2596485 := by exact prefixLift 2596485
  have htrace : WordTrace (prefixWord ++ tailWord_2596485) baseStart_2596485 baseEnd_2596485 := by
    simpa [prefixWord, tailWord_2596485, baseEnd_2596485] using wordTrace_append hprefix tailTrace_2596485
  have hstable : (prefixWord ++ tailWord_2596485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596485).length < 2 ^ (prefixWord ++ tailWord_2596485).sum := by decide
  have hdescent : baseEnd_2596485 < baseStart_2596485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596525 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2596525 : Nat := 118140960795 + 2596525 * 2 ^ 59
def prefixEnd_2596525 : Nat := 4983230072969 + 3 ^ 40 * 2596525 * 2
def baseEnd_2596525 : Nat := 1333265356415558817696305

theorem tailTrace_2596525 : CollatzResearch.WordTrace tailWord_2596525 prefixEnd_2596525 1333265356415558817696305 := by
  unfold tailWord_2596525
  simp only [CollatzResearch.WordTrace]
  refine ⟨94703046918240851010159029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63135364612160567340106019 94703046918240851010159029)
  ·
    refine ⟨8878410648585079782202409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94703046918240851010159029 8878410648585079782202409)
    ·
      refine ⟨6658807986438809836651807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8878410648585079782202409 6658807986438809836651807)
      ·
        refine ⟨9988211979658214754977711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6658807986438809836651807 9988211979658214754977711)
        ·
          refine ⟨14982317969487322132466567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9988211979658214754977711 14982317969487322132466567)
          ·
            refine ⟨22473476954230983198699851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14982317969487322132466567 22473476954230983198699851)
            ·
              refine ⟨33710215431346474798049777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22473476954230983198699851 33710215431346474798049777)
              ·
                refine ⟨25282661573509856098537333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33710215431346474798049777 25282661573509856098537333)
                ·
                  refine ⟨2370249522516549009237875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25282661573509856098537333 2370249522516549009237875)
                  ·
                    refine ⟨3555374283774823513856813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2370249522516549009237875 3555374283774823513856813)
                    ·
                      refine ⟨1333265356415558817696305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3555374283774823513856813 1333265356415558817696305)
                      ·
                        rfl

theorem cell23_2596525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2596525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596525 prefixEnd_2596525 := by exact prefixLift 2596525
  have htrace : WordTrace (prefixWord ++ tailWord_2596525) baseStart_2596525 baseEnd_2596525 := by
    simpa [prefixWord, tailWord_2596525, baseEnd_2596525] using wordTrace_append hprefix tailTrace_2596525
  have hstable : (prefixWord ++ tailWord_2596525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596525).length < 2 ^ (prefixWord ++ tailWord_2596525).sum := by decide
  have hdescent : baseEnd_2596525 < baseStart_2596525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596542 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2596542 : Nat := 118140960795 + 2596542 * 2 ^ 59
def prefixEnd_2596542 : Nat := 4983230072969 + 3 ^ 40 * 2596542 * 2
def baseEnd_2596542 : Nat := 1333274085586685251183727

theorem tailTrace_2596542 : CollatzResearch.WordTrace tailWord_2596542 prefixEnd_2596542 1333274085586685251183727 := by
  unfold tailWord_2596542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11837958369897407864190985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63135777972786175275685253 11837958369897407864190985)
  ·
    refine ⟨8878468777423055898143239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11837958369897407864190985 8878468777423055898143239)
    ·
      refine ⟨13317703166134583847214859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8878468777423055898143239 13317703166134583847214859)
      ·
        refine ⟨19976554749201875770822289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13317703166134583847214859 19976554749201875770822289)
        ·
          refine ⟨14982416061901406828116717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19976554749201875770822289 14982416061901406828116717)
          ·
            refine ⟨5618406023213027560543769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14982416061901406828116717 5618406023213027560543769)
            ·
              refine ⟨4213804517409770670407827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5618406023213027560543769 4213804517409770670407827)
              ·
                refine ⟨6320706776114656005611741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4213804517409770670407827 6320706776114656005611741)
                ·
                  refine ⟨2370265041042996002104403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6320706776114656005611741 2370265041042996002104403)
                  ·
                    refine ⟨3555397561564494003156605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2370265041042996002104403 3555397561564494003156605)
                    ·
                      refine ⟨1333274085586685251183727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3555397561564494003156605 1333274085586685251183727)
                      ·
                        rfl

theorem cell23_2596542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2596542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596542 prefixEnd_2596542 := by exact prefixLift 2596542
  have htrace : WordTrace (prefixWord ++ tailWord_2596542) baseStart_2596542 baseEnd_2596542 := by
    simpa [prefixWord, tailWord_2596542, baseEnd_2596542] using wordTrace_append hprefix tailTrace_2596542
  have hstable : (prefixWord ++ tailWord_2596542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596542).length < 2 ^ (prefixWord ++ tailWord_2596542).sum := by decide
  have hdescent : baseEnd_2596542 < baseStart_2596542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596668 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2596668 : Nat := 118140960795 + 2596668 * 2 ^ 59
def prefixEnd_2596668 : Nat := 4983230072969 + 3 ^ 40 * 2596668 * 2
def baseEnd_2596668 : Nat := 1333338784149151758208147

theorem tailTrace_2596668 : CollatzResearch.WordTrace tailWord_2596668 prefixEnd_2596668 1333338784149151758208147 := by
  unfold tailWord_2596668
  simp only [CollatzResearch.WordTrace]
  refine ⟨47354131278361393216307329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63138841704481857621743105 47354131278361393216307329)
  ·
    refine ⟨35515598458771044912230497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47354131278361393216307329 35515598458771044912230497)
    ·
      refine ⟨26636698844078283684172873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35515598458771044912230497 26636698844078283684172873)
      ·
        refine ⟨19977524133058712763129655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26636698844078283684172873 19977524133058712763129655)
        ·
          refine ⟨29966286199588069144694483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19977524133058712763129655 29966286199588069144694483)
          ·
            refine ⟨44949429299382103717041725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29966286199588069144694483 44949429299382103717041725)
            ·
              refine ⟨16856035987268288893890647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44949429299382103717041725 16856035987268288893890647)
              ·
                refine ⟨25284053980902433340835971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16856035987268288893890647 25284053980902433340835971)
                ·
                  refine ⟨37926080971353650011253957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25284053980902433340835971 37926080971353650011253957)
                  ·
                    refine ⟨7111140182128809377110117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37926080971353650011253957 7111140182128809377110117)
                    ·
                      refine ⟨1333338784149151758208147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7111140182128809377110117 1333338784149151758208147)
                      ·
                        rfl

theorem cell23_2596668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2596668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596668 prefixEnd_2596668 := by exact prefixLift 2596668
  have htrace : WordTrace (prefixWord ++ tailWord_2596668) baseStart_2596668 baseEnd_2596668 := by
    simpa [prefixWord, tailWord_2596668, baseEnd_2596668] using wordTrace_append hprefix tailTrace_2596668
  have hstable : (prefixWord ++ tailWord_2596668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596668).length < 2 ^ (prefixWord ++ tailWord_2596668).sum := by decide
  have hdescent : baseEnd_2596668 < baseStart_2596668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596688 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_2596688 : Nat := 118140960795 + 2596688 * 2 ^ 59
def prefixEnd_2596688 : Nat := 4983230072969 + 3 ^ 40 * 2596688 * 2
def baseEnd_2596688 : Nat := 1333349053762241679958055

theorem tailTrace_2596688 : CollatzResearch.WordTrace tailWord_2596688 prefixEnd_2596688 1333349053762241679958055 := by
  unfold tailWord_2596688
  simp only [CollatzResearch.WordTrace]
  refine ⟨47354496008325164924171359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63139328011100219898895145 47354496008325164924171359)
  ·
    refine ⟨71031744012487747386257039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47354496008325164924171359 71031744012487747386257039)
    ·
      refine ⟨106547616018731621079385559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71031744012487747386257039 106547616018731621079385559)
      ·
        refine ⟨159821424028097431619078339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106547616018731621079385559 159821424028097431619078339)
        ·
          refine ⟨239732136042146147428617509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159821424028097431619078339 239732136042146147428617509)
          ·
            refine ⟨44949775507902402642865783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239732136042146147428617509 44949775507902402642865783)
            ·
              refine ⟨67424663261853603964298675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44949775507902402642865783 67424663261853603964298675)
              ·
                refine ⟨101136994892780405946448013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67424663261853603964298675 101136994892780405946448013)
                ·
                  refine ⟨37926373084792652229918005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101136994892780405946448013 37926373084792652229918005)
                  ·
                    refine ⟨3555597476699311146554813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37926373084792652229918005 3555597476699311146554813)
                    ·
                      refine ⟨1333349053762241679958055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3555597476699311146554813 1333349053762241679958055)
                      ·
                        rfl

theorem cell23_2596688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_2596688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596688 prefixEnd_2596688 := by exact prefixLift 2596688
  have htrace : WordTrace (prefixWord ++ tailWord_2596688) baseStart_2596688 baseEnd_2596688 := by
    simpa [prefixWord, tailWord_2596688, baseEnd_2596688] using wordTrace_append hprefix tailTrace_2596688
  have hstable : (prefixWord ++ tailWord_2596688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596688).length < 2 ^ (prefixWord ++ tailWord_2596688).sum := by decide
  have hdescent : baseEnd_2596688 < baseStart_2596688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596706 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_2596706 : Nat := 118140960795 + 2596706 * 2 ^ 59
def prefixEnd_2596706 : Nat := 4983230072969 + 3 ^ 40 * 2596706 * 2
def baseEnd_2596706 : Nat := 1333358296414022609532973

theorem tailTrace_2596706 : CollatzResearch.WordTrace tailWord_2596706 prefixEnd_2596706 1333358296414022609532973 := by
  unfold tailWord_2596706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677412132646279730624493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63139765687056745948331981 23677412132646279730624493)
  ·
    refine ⟨8879029549742354898984185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23677412132646279730624493 8879029549742354898984185)
    ·
      refine ⟨6659272162306766174238139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8879029549742354898984185 6659272162306766174238139)
      ·
        refine ⟨9988908243460149261357209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6659272162306766174238139 9988908243460149261357209)
        ·
          refine ⟨7491681182595111946017907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9988908243460149261357209 7491681182595111946017907)
          ·
            refine ⟨11237521773892667919026861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7491681182595111946017907 11237521773892667919026861)
            ·
              refine ⟨4214070665209750469635073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11237521773892667919026861 4214070665209750469635073)
              ·
                refine ⟨3160552998907312852226305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4214070665209750469635073 3160552998907312852226305)
                ·
                  refine ⟨2370414749180484639169729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3160552998907312852226305 2370414749180484639169729)
                  ·
                    refine ⟨1777811061885363479377297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2370414749180484639169729 1777811061885363479377297)
                    ·
                      refine ⟨1333358296414022609532973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777811061885363479377297 1333358296414022609532973)
                      ·
                        rfl

theorem cell23_2596706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_2596706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596706 prefixEnd_2596706 := by exact prefixLift 2596706
  have htrace : WordTrace (prefixWord ++ tailWord_2596706) baseStart_2596706 baseEnd_2596706 := by
    simpa [prefixWord, tailWord_2596706, baseEnd_2596706] using wordTrace_append hprefix tailTrace_2596706
  have hstable : (prefixWord ++ tailWord_2596706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596706).length < 2 ^ (prefixWord ++ tailWord_2596706).sum := by decide
  have hdescent : baseEnd_2596706 < baseStart_2596706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596745 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_2596745 : Nat := 118140960795 + 2596745 * 2 ^ 59
def prefixEnd_2596745 : Nat := 4983230072969 + 3 ^ 40 * 2596745 * 2
def baseEnd_2596745 : Nat := 1333378322159547956945293

theorem tailTrace_2596745 : CollatzResearch.WordTrace tailWord_2596745 prefixEnd_2596745 1333378322159547956945293 := by
  unfold tailWord_2596745
  simp only [CollatzResearch.WordTrace]
  refine ⟨94711070977443828583167689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63140713984962552388778459 94711070977443828583167689)
  ·
    refine ⟨71033303233082871437375767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94711070977443828583167689 71033303233082871437375767)
    ·
      refine ⟨106549954849624307156063651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71033303233082871437375767 106549954849624307156063651)
      ·
        refine ⟨159824932274436460734095477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106549954849624307156063651 159824932274436460734095477)
        ·
          refine ⟨14983587400728418193821451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159824932274436460734095477 14983587400728418193821451)
          ·
            refine ⟨22475381101092627290732177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14983587400728418193821451 22475381101092627290732177)
            ·
              refine ⟨16856535825819470468049133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22475381101092627290732177 16856535825819470468049133)
              ·
                refine ⟨6321200934682301425518425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16856535825819470468049133 6321200934682301425518425)
                ·
                  refine ⟨4740900701011726069138819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321200934682301425518425 4740900701011726069138819)
                  ·
                    refine ⟨7111351051517589103708229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4740900701011726069138819 7111351051517589103708229)
                    ·
                      refine ⟨1333378322159547956945293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7111351051517589103708229 1333378322159547956945293)
                      ·
                        rfl

theorem cell23_2596745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_2596745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596745 prefixEnd_2596745 := by exact prefixLift 2596745
  have htrace : WordTrace (prefixWord ++ tailWord_2596745) baseStart_2596745 baseEnd_2596745 := by
    simpa [prefixWord, tailWord_2596745, baseEnd_2596745] using wordTrace_append hprefix tailTrace_2596745
  have hstable : (prefixWord ++ tailWord_2596745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596745).length < 2 ^ (prefixWord ++ tailWord_2596745).sum := by decide
  have hdescent : baseEnd_2596745 < baseStart_2596745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596746 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_2596746 : Nat := 118140960795 + 2596746 * 2 ^ 59
def prefixEnd_2596746 : Nat := 4983230072969 + 3 ^ 40 * 2596746 * 2
def baseEnd_2596746 : Nat := 148153203960022494781421

theorem tailTrace_2596746 : CollatzResearch.WordTrace tailWord_2596746 prefixEnd_2596746 148153203960022494781421 := by
  unfold tailWord_2596746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677776862610051438488523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63140738300293470502636061 23677776862610051438488523)
  ·
    refine ⟨35516665293915077157732785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23677776862610051438488523 35516665293915077157732785)
    ·
      refine ⟨26637498970436307868299589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35516665293915077157732785 26637498970436307868299589)
      ·
        refine ⟨4994531056956807725306173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26637498970436307868299589 4994531056956807725306173)
        ·
          refine ⟨1872949146358802896989815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4994531056956807725306173 1872949146358802896989815)
          ·
            refine ⟨2809423719538204345484723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872949146358802896989815 2809423719538204345484723)
            ·
              refine ⟨4214135579307306518227085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809423719538204345484723 4214135579307306518227085)
              ·
                refine ⟨1580300842240239944335157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4214135579307306518227085 1580300842240239944335157)
                ·
                  refine ⟨148153203960022494781421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580300842240239944335157 148153203960022494781421)
                  ·
                    rfl

theorem cell23_2596746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_2596746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596746 prefixEnd_2596746 := by exact prefixLift 2596746
  have htrace : WordTrace (prefixWord ++ tailWord_2596746) baseStart_2596746 baseEnd_2596746 := by
    simpa [prefixWord, tailWord_2596746, baseEnd_2596746] using wordTrace_append hprefix tailTrace_2596746
  have hstable : (prefixWord ++ tailWord_2596746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596746).length < 2 ^ (prefixWord ++ tailWord_2596746).sum := by decide
  have hdescent : baseEnd_2596746 < baseStart_2596746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596748 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2596748 : Nat := 118140960795 + 2596748 * 2 ^ 59
def prefixEnd_2596748 : Nat := 4983230072969 + 3 ^ 40 * 2596748 * 2
def baseEnd_2596748 : Nat := 1333379862601511445207779

theorem tailTrace_2596748 : CollatzResearch.WordTrace tailWord_2596748 prefixEnd_2596748 1333379862601511445207779 := by
  unfold tailWord_2596748
  simp only [CollatzResearch.WordTrace]
  refine ⟨47355590198216480047763449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63140786930955306730351265 47355590198216480047763449)
  ·
    refine ⟨35516692648662360035822587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47355590198216480047763449 35516692648662360035822587)
    ·
      refine ⟨53275038972993540053733881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35516692648662360035822587 53275038972993540053733881)
      ·
        refine ⟨39956279229745155040300411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53275038972993540053733881 39956279229745155040300411)
        ·
          refine ⟨59934418844617732560450617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39956279229745155040300411 59934418844617732560450617)
          ·
            refine ⟨44950814133463299420337963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59934418844617732560450617 44950814133463299420337963)
            ·
              refine ⟨67426221200194949130506945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44950814133463299420337963 67426221200194949130506945)
              ·
                refine ⟨50569665900146211847880209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67426221200194949130506945 50569665900146211847880209)
                ·
                  refine ⟨37927249425109658885910157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50569665900146211847880209 37927249425109658885910157)
                  ·
                    refine ⟨14222718534416122082216309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37927249425109658885910157 14222718534416122082216309)
                    ·
                      refine ⟨1333379862601511445207779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14222718534416122082216309 1333379862601511445207779)
                      ·
                        rfl

theorem cell23_2596748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2596748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596748 prefixEnd_2596748 := by exact prefixLift 2596748
  have htrace : WordTrace (prefixWord ++ tailWord_2596748) baseStart_2596748 baseEnd_2596748 := by
    simpa [prefixWord, tailWord_2596748, baseEnd_2596748] using wordTrace_append hprefix tailTrace_2596748
  have hstable : (prefixWord ++ tailWord_2596748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596748).length < 2 ^ (prefixWord ++ tailWord_2596748).sum := by decide
  have hdescent : baseEnd_2596748 < baseStart_2596748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596762 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2596762 : Nat := 118140960795 + 2596762 * 2 ^ 59
def prefixEnd_2596762 : Nat := 4983230072969 + 3 ^ 40 * 2596762 * 2
def baseEnd_2596762 : Nat := 1333387051330674390432715

theorem tailTrace_2596762 : CollatzResearch.WordTrace tailWord_2596762 prefixEnd_2596762 1333387051330674390432715 := by
  unfold tailWord_2596762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677922754595560121634135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63141127345588160324357693 23677922754595560121634135)
  ·
    refine ⟨35516884131893340182451203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23677922754595560121634135 35516884131893340182451203)
    ·
      refine ⟨53275326197840010273676805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35516884131893340182451203 53275326197840010273676805)
      ·
        refine ⟨9989123662095001926314401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53275326197840010273676805 9989123662095001926314401)
        ·
          refine ⟨7491842746571251444735801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9989123662095001926314401 7491842746571251444735801)
          ·
            refine ⟨5618882059928438583551851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7491842746571251444735801 5618882059928438583551851)
            ·
              refine ⟨8428323089892657875327777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5618882059928438583551851 8428323089892657875327777)
              ·
                refine ⟨6321242317419493406495833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8428323089892657875327777 6321242317419493406495833)
                ·
                  refine ⟨4740931738064620054871875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321242317419493406495833 4740931738064620054871875)
                  ·
                    refine ⟨7111397607096930082307813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4740931738064620054871875 7111397607096930082307813)
                    ·
                      refine ⟨1333387051330674390432715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7111397607096930082307813 1333387051330674390432715)
                      ·
                        rfl

theorem cell23_2596762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2596762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596762 prefixEnd_2596762 := by exact prefixLift 2596762
  have htrace : WordTrace (prefixWord ++ tailWord_2596762) baseStart_2596762 baseEnd_2596762 := by
    simpa [prefixWord, tailWord_2596762, baseEnd_2596762] using wordTrace_append hprefix tailTrace_2596762
  have hstable : (prefixWord ++ tailWord_2596762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596762).length < 2 ^ (prefixWord ++ tailWord_2596762).sum := by decide
  have hdescent : baseEnd_2596762 < baseStart_2596762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596772 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_2596772 : Nat := 118140960795 + 2596772 * 2 ^ 59
def prefixEnd_2596772 : Nat := 4983230072969 + 3 ^ 40 * 2596772 * 2
def baseEnd_2596772 : Nat := 444464062045739783769223

theorem tailTrace_2596772 : CollatzResearch.WordTrace tailWord_2596772 prefixEnd_2596772 444464062045739783769223 := by
  unfold tailWord_2596772
  simp only [CollatzResearch.WordTrace]
  refine ⟨47356027874173006097200285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63141370498897341462933713 47356027874173006097200285)
  ·
    refine ⟨17758510452814877286450107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47356027874173006097200285 17758510452814877286450107)
    ·
      refine ⟨26637765679222315929675161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17758510452814877286450107 26637765679222315929675161)
      ·
        refine ⟨19978324259416736947256371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26637765679222315929675161 19978324259416736947256371)
        ·
          refine ⟨29967486389125105420884557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19978324259416736947256371 29967486389125105420884557)
          ·
            refine ⟨11237807395921914532831709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29967486389125105420884557 11237807395921914532831709)
            ·
              refine ⟨4214177773470717949811891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11237807395921914532831709 4214177773470717949811891)
              ·
                refine ⟨6321266660206076924717837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214177773470717949811891 6321266660206076924717837)
                ·
                  refine ⟨2370474997577278846769189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6321266660206076924717837 2370474997577278846769189)
                  ·
                    refine ⟨444464062045739783769223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2370474997577278846769189 444464062045739783769223)
                    ·
                      rfl

theorem cell23_2596772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_2596772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596772 prefixEnd_2596772 := by exact prefixLift 2596772
  have htrace : WordTrace (prefixWord ++ tailWord_2596772) baseStart_2596772 baseEnd_2596772 := by
    simpa [prefixWord, tailWord_2596772, baseEnd_2596772] using wordTrace_append hprefix tailTrace_2596772
  have hstable : (prefixWord ++ tailWord_2596772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596772).length < 2 ^ (prefixWord ++ tailWord_2596772).sum := by decide
  have hdescent : baseEnd_2596772 < baseStart_2596772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596869 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 1, 1, 4]
def baseStart_2596869 : Nat := 118140960795 + 2596869 * 2 ^ 59
def prefixEnd_2596869 : Nat := 4983230072969 + 3 ^ 40 * 2596869 * 2
def baseEnd_2596869 : Nat := 1333441993760705471794723

theorem tailTrace_2596869 : CollatzResearch.WordTrace tailWord_2596869 prefixEnd_2596869 1333441993760705471794723 := by
  unfold tailWord_2596869
  simp only [CollatzResearch.WordTrace]
  refine ⟨94715593628994597760681661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63143729085996398507121107 94715593628994597760681661)
  ·
    refine ⟨35518347610872974160255623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94715593628994597760681661 35518347610872974160255623)
    ·
      refine ⟨53277521416309461240383435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35518347610872974160255623 53277521416309461240383435)
      ·
        refine ⟨79916282124464191860575153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53277521416309461240383435 79916282124464191860575153)
        ·
          refine ⟨59937211593348143895431365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79916282124464191860575153 59937211593348143895431365)
          ·
            refine ⟨11238227173752776980393381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59937211593348143895431365 11238227173752776980393381)
            ·
              refine ⟨2107167595078645683823759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11238227173752776980393381 2107167595078645683823759)
              ·
                refine ⟨3160751392617968525735639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107167595078645683823759 3160751392617968525735639)
                ·
                  refine ⟨4741127088926952788603459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160751392617968525735639 4741127088926952788603459)
                  ·
                    refine ⟨7111690633390429182905189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4741127088926952788603459 7111690633390429182905189)
                    ·
                      refine ⟨1333441993760705471794723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7111690633390429182905189 1333441993760705471794723)
                      ·
                        rfl

theorem cell23_2596869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_2596869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596869 prefixEnd_2596869 := by exact prefixLift 2596869
  have htrace : WordTrace (prefixWord ++ tailWord_2596869) baseStart_2596869 baseEnd_2596869 := by
    simpa [prefixWord, tailWord_2596869, baseEnd_2596869] using wordTrace_append hprefix tailTrace_2596869
  have hstable : (prefixWord ++ tailWord_2596869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596869).length < 2 ^ (prefixWord ++ tailWord_2596869).sum := by decide
  have hdescent : baseEnd_2596869 < baseStart_2596869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596870 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2596870 : Nat := 118140960795 + 2596870 * 2 ^ 59
def prefixEnd_2596870 : Nat := 4983230072969 + 3 ^ 40 * 2596870 * 2
def baseEnd_2596870 : Nat := 148160278582373329764691

theorem tailTrace_2596870 : CollatzResearch.WordTrace tailWord_2596870 prefixEnd_2596870 148160278582373329764691 := by
  unfold tailWord_2596870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959863440687217966608377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63143753401327316620978709 2959863440687217966608377)
  ·
    refine ⟨2219897580515413474956283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2959863440687217966608377 2219897580515413474956283)
    ·
      refine ⟨3329846370773120212434425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2219897580515413474956283 3329846370773120212434425)
      ·
        refine ⟨2497384778079840159325819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3329846370773120212434425 2497384778079840159325819)
        ·
          refine ⟨3746077167119760238988729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2497384778079840159325819 3746077167119760238988729)
          ·
            refine ⟨2809557875339820179241547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746077167119760238988729 2809557875339820179241547)
            ·
              refine ⟨4214336813009730268862321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809557875339820179241547 4214336813009730268862321)
              ·
                refine ⟨3160752609757297701646741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4214336813009730268862321 3160752609757297701646741)
                ·
                  refine ⟨148160278582373329764691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3160752609757297701646741 148160278582373329764691)
                  ·
                    rfl

theorem cell23_2596870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2596870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596870 prefixEnd_2596870 := by exact prefixLift 2596870
  have htrace : WordTrace (prefixWord ++ tailWord_2596870) baseStart_2596870 baseEnd_2596870 := by
    simpa [prefixWord, tailWord_2596870, baseEnd_2596870] using wordTrace_append hprefix tailTrace_2596870
  have hstable : (prefixWord ++ tailWord_2596870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596870).length < 2 ^ (prefixWord ++ tailWord_2596870).sum := by decide
  have hdescent : baseEnd_2596870 < baseStart_2596870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596906 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2596906 : Nat := 118140960795 + 2596906 * 2 ^ 59
def prefixEnd_2596906 : Nat := 4983230072969 + 3 ^ 40 * 2596906 * 2
def baseEnd_2596906 : Nat := 1333460992544921827032053

theorem tailTrace_2596906 : CollatzResearch.WordTrace tailWord_2596906 prefixEnd_2596906 1333460992544921827032053 := by
  unfold tailWord_2596906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679235782465138269944643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63144628753240368719852381 23679235782465138269944643)
  ·
    refine ⟨35518853673697707404916965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23679235782465138269944643 35518853673697707404916965)
    ·
      refine ⟨6659785063818320138421931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35518853673697707404916965 6659785063818320138421931)
      ·
        refine ⟨9989677595727480207632897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6659785063818320138421931 9989677595727480207632897)
        ·
          refine ⟨7492258196795610155724673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9989677595727480207632897 7492258196795610155724673)
          ·
            refine ⟨5619193647596707616793505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7492258196795610155724673 5619193647596707616793505)
            ·
              refine ⟨4214395235697530712595129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5619193647596707616793505 4214395235697530712595129)
              ·
                refine ⟨3160796426773148034446347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4214395235697530712595129 3160796426773148034446347)
                ·
                  refine ⟨4741194640159722051669521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160796426773148034446347 4741194640159722051669521)
                  ·
                    refine ⟨3555895980119791538752141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4741194640159722051669521 3555895980119791538752141)
                    ·
                      refine ⟨1333460992544921827032053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3555895980119791538752141 1333460992544921827032053)
                      ·
                        rfl

theorem cell23_2596906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2596906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596906 prefixEnd_2596906 := by exact prefixLift 2596906
  have htrace : WordTrace (prefixWord ++ tailWord_2596906) baseStart_2596906 baseEnd_2596906 := by
    simpa [prefixWord, tailWord_2596906, baseEnd_2596906] using wordTrace_append hprefix tailTrace_2596906
  have hstable : (prefixWord ++ tailWord_2596906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596906).length < 2 ^ (prefixWord ++ tailWord_2596906).sum := by decide
  have hdescent : baseEnd_2596906 < baseStart_2596906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596915 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_2596915 : Nat := 118140960795 + 2596915 * 2 ^ 59
def prefixEnd_2596915 : Nat := 4983230072969 + 3 ^ 40 * 2596915 * 2
def baseEnd_2596915 : Nat := 1333465613870812291819511

theorem tailTrace_2596915 : CollatzResearch.WordTrace tailWord_2596915 prefixEnd_2596915 1333465613870812291819511 := by
  unfold tailWord_2596915
  simp only [CollatzResearch.WordTrace]
  refine ⟨94717271386827947616856199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63144847591218631744570799 94717271386827947616856199)
  ·
    refine ⟨142075907080241921425284299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94717271386827947616856199 142075907080241921425284299)
    ·
      refine ⟨213113860620362882137926449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142075907080241921425284299 213113860620362882137926449)
      ·
        refine ⟨159835395465272161603444837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213113860620362882137926449 159835395465272161603444837)
        ·
          refine ⟨29969136649738530300645907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159835395465272161603444837 29969136649738530300645907)
          ·
            refine ⟨44953704974607795450968861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29969136649738530300645907 44953704974607795450968861)
            ·
              refine ⟨16857639365477923294113323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44953704974607795450968861 16857639365477923294113323)
              ·
                refine ⟨25286459048216884941169985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16857639365477923294113323 25286459048216884941169985)
                ·
                  refine ⟨18964844286162663705877489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25286459048216884941169985 18964844286162663705877489)
                  ·
                    refine ⟨14223633214621997779408117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18964844286162663705877489 14223633214621997779408117)
                    ·
                      refine ⟨1333465613870812291819511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14223633214621997779408117 1333465613870812291819511)
                      ·
                        rfl

theorem cell23_2596915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_2596915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596915 prefixEnd_2596915 := by exact prefixLift 2596915
  have htrace : WordTrace (prefixWord ++ tailWord_2596915) baseStart_2596915 baseEnd_2596915 := by
    simpa [prefixWord, tailWord_2596915, baseEnd_2596915] using wordTrace_append hprefix tailTrace_2596915
  have hstable : (prefixWord ++ tailWord_2596915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596915).length < 2 ^ (prefixWord ++ tailWord_2596915).sum := by decide
  have hdescent : baseEnd_2596915 < baseStart_2596915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596920 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 1, 2, 2]
def baseStart_2596920 : Nat := 118140960795 + 2596920 * 2 ^ 59
def prefixEnd_2596920 : Nat := 4983230072969 + 3 ^ 40 * 2596920 * 2
def baseEnd_2596920 : Nat := 1333468181274084772256989

theorem tailTrace_2596920 : CollatzResearch.WordTrace tailWord_2596920 prefixEnd_2596920 1333468181274084772256989 := by
  unfold tailWord_2596920
  simp only [CollatzResearch.WordTrace]
  refine ⟨47358726875904916735394107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63144969167873222313858809 47358726875904916735394107)
  ·
    refine ⟨71038090313857375103091161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47358726875904916735394107 71038090313857375103091161)
    ·
      refine ⟨53278567735393031327318371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71038090313857375103091161 53278567735393031327318371)
      ·
        refine ⟨79917851603089546990977557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53278567735393031327318371 79917851603089546990977557)
        ·
          refine ⟨3746149293894822515202073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79917851603089546990977557 3746149293894822515202073)
          ·
            refine ⟨2809611970421116886401555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746149293894822515202073 2809611970421116886401555)
            ·
              refine ⟨4214417955631675329602333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809611970421116886401555 4214417955631675329602333)
              ·
                refine ⟨1580406733361878248600875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4214417955631675329602333 1580406733361878248600875)
                ·
                  refine ⟨2370610100042817372901313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580406733361878248600875 2370610100042817372901313)
                  ·
                    refine ⟨1777957575032113029675985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2370610100042817372901313 1777957575032113029675985)
                    ·
                      refine ⟨1333468181274084772256989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777957575032113029675985 1333468181274084772256989)
                      ·
                        rfl

theorem cell23_2596920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_2596920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596920 prefixEnd_2596920 := by exact prefixLift 2596920
  have htrace : WordTrace (prefixWord ++ tailWord_2596920) baseStart_2596920 baseEnd_2596920 := by
    simpa [prefixWord, tailWord_2596920, baseEnd_2596920] using wordTrace_append hprefix tailTrace_2596920
  have hstable : (prefixWord ++ tailWord_2596920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596920).length < 2 ^ (prefixWord ++ tailWord_2596920).sum := by decide
  have hdescent : baseEnd_2596920 < baseStart_2596920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596945 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_2596945 : Nat := 118140960795 + 2596945 * 2 ^ 59
def prefixEnd_2596945 : Nat := 4983230072969 + 3 ^ 40 * 2596945 * 2
def baseEnd_2596945 : Nat := 1333481018290447174444373

theorem tailTrace_2596945 : CollatzResearch.WordTrace tailWord_2596945 prefixEnd_2596945 1333481018290447174444373 := by
  unfold tailWord_2596945
  simp only [CollatzResearch.WordTrace]
  refine ⟨94718365576719262740448289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63145577051146175160298859 94718365576719262740448289)
  ·
    refine ⟨71038774182539447055336217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94718365576719262740448289 71038774182539447055336217)
    ·
      refine ⟨53279080636904585291502163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71038774182539447055336217 53279080636904585291502163)
      ·
        refine ⟨79918620955356877937253245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53279080636904585291502163 79918620955356877937253245)
        ·
          refine ⟨29969482858258829226469967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79918620955356877937253245 29969482858258829226469967)
          ·
            refine ⟨44954224287388243839704951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29969482858258829226469967 44954224287388243839704951)
            ·
              refine ⟨67431336431082365759557427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44954224287388243839704951 67431336431082365759557427)
              ·
                refine ⟨101147004646623548639336141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67431336431082365759557427 101147004646623548639336141)
                ·
                  refine ⟨37930126742483830739751053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101147004646623548639336141 37930126742483830739751053)
                  ·
                    refine ⟨14223797528431436527406645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37930126742483830739751053 14223797528431436527406645)
                    ·
                      refine ⟨1333481018290447174444373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14223797528431436527406645 1333481018290447174444373)
                      ·
                        rfl

theorem cell23_2596945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_2596945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596945 prefixEnd_2596945 := by exact prefixLift 2596945
  have htrace : WordTrace (prefixWord ++ tailWord_2596945) baseStart_2596945 baseEnd_2596945 := by
    simpa [prefixWord, tailWord_2596945, baseEnd_2596945] using wordTrace_append hprefix tailTrace_2596945
  have hstable : (prefixWord ++ tailWord_2596945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596945).length < 2 ^ (prefixWord ++ tailWord_2596945).sum := by decide
  have hdescent : baseEnd_2596945 < baseStart_2596945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596959 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 6, 2, 2]
def baseStart_2596959 : Nat := 118140960795 + 2596959 * 2 ^ 59
def prefixEnd_2596959 : Nat := 4983230072969 + 3 ^ 40 * 2596959 * 2
def baseEnd_2596959 : Nat := 1333488207019610119669309

theorem tailTrace_2596959 : CollatzResearch.WordTrace tailWord_2596959 prefixEnd_2596959 1333488207019610119669309 := by
  unfold tailWord_2596959
  simp only [CollatzResearch.WordTrace]
  refine ⟨94718876198668543131457931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63145917465779028754305287 94718876198668543131457931)
  ·
    refine ⟨142078314298002814697186897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94718876198668543131457931 142078314298002814697186897)
    ·
      refine ⟨106558735723502111022890173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142078314298002814697186897 106558735723502111022890173)
      ·
        refine ⟨39959525896313291633583815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106558735723502111022890173 39959525896313291633583815)
        ·
          refine ⟨59939288844469937450375723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39959525896313291633583815 59939288844469937450375723)
          ·
            refine ⟨89908933266704906175563585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59939288844469937450375723 89908933266704906175563585)
            ·
              refine ⟨67431699950028679631672689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89908933266704906175563585 67431699950028679631672689)
              ·
                refine ⟨50573774962521509723754517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67431699950028679631672689 50573774962521509723754517)
                ·
                  refine ⟨2370645701368195768300993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50573774962521509723754517 2370645701368195768300993)
                  ·
                    refine ⟨1777984276026146826225745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2370645701368195768300993 1777984276026146826225745)
                    ·
                      refine ⟨1333488207019610119669309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1777984276026146826225745 1333488207019610119669309)
                      ·
                        rfl

theorem cell23_2596959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_2596959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596959 prefixEnd_2596959 := by exact prefixLift 2596959
  have htrace : WordTrace (prefixWord ++ tailWord_2596959) baseStart_2596959 baseEnd_2596959 := by
    simpa [prefixWord, tailWord_2596959, baseEnd_2596959] using wordTrace_append hprefix tailTrace_2596959
  have hstable : (prefixWord ++ tailWord_2596959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596959).length < 2 ^ (prefixWord ++ tailWord_2596959).sum := by decide
  have hdescent : baseEnd_2596959 < baseStart_2596959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596992 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_2596992 : Nat := 118140960795 + 2596992 * 2 ^ 59
def prefixEnd_2596992 : Nat := 4983230072969 + 3 ^ 40 * 2596992 * 2
def baseEnd_2596992 : Nat := 1333505151881208490556657

theorem tailTrace_2596992 : CollatzResearch.WordTrace tailWord_2596992 prefixEnd_2596992 1333505151881208490556657 := by
  unfold tailWord_2596992
  simp only [CollatzResearch.WordTrace]
  refine ⟨47360039903774494883704615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63146719871699326511606153 47360039903774494883704615)
  ·
    refine ⟨71040059855661742325556923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47360039903774494883704615 71040059855661742325556923)
    ·
      refine ⟨106560089783492613488335385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71040059855661742325556923 106560089783492613488335385)
      ·
        refine ⟨79920067337619460116251539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106560089783492613488335385 79920067337619460116251539)
        ·
          refine ⟨119880101006429190174377309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79920067337619460116251539 119880101006429190174377309)
          ·
            refine ⟨44955037877410946315391491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119880101006429190174377309 44955037877410946315391491)
            ·
              refine ⟨67432556816116419473087237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44955037877410946315391491 67432556816116419473087237)
              ·
                refine ⟨12643604403021828651203857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67432556816116419473087237 12643604403021828651203857)
                ·
                  refine ⟨9482703302266371488402893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12643604403021828651203857 9482703302266371488402893)
                  ·
                    refine ⟨3556013738349889308151085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9482703302266371488402893 3556013738349889308151085)
                    ·
                      refine ⟨1333505151881208490556657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3556013738349889308151085 1333505151881208490556657)
                      ·
                        rfl

theorem cell23_2596992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_2596992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2596992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2596992 prefixEnd_2596992 := by exact prefixLift 2596992
  have htrace : WordTrace (prefixWord ++ tailWord_2596992) baseStart_2596992 baseEnd_2596992 := by
    simpa [prefixWord, tailWord_2596992, baseEnd_2596992] using wordTrace_append hprefix tailTrace_2596992
  have hstable : (prefixWord ++ tailWord_2596992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596992).length < 2 ^ (prefixWord ++ tailWord_2596992).sum := by decide
  have hdescent : baseEnd_2596992 < baseStart_2596992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597049 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 4, 4, 2]
def baseStart_2597049 : Nat := 118140960795 + 2597049 * 2 ^ 59
def prefixEnd_2597049 : Nat := 4983230072969 + 3 ^ 40 * 2597049 * 2
def baseEnd_2597049 : Nat := 1333534420278514767543895

theorem tailTrace_2597049 : CollatzResearch.WordTrace tailWord_2597049 prefixEnd_2597049 1333534420278514767543895 := by
  unfold tailWord_2597049
  simp only [CollatzResearch.WordTrace]
  refine ⟨94722158768342488502234201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63148105845561659001489467 94722158768342488502234201)
  ·
    refine ⟨71041619076256866376675651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94722158768342488502234201 71041619076256866376675651)
    ·
      refine ⟨106562428614385299565013477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71041619076256866376675651 106562428614385299565013477)
      ·
        refine ⟨19980455365197243668440027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106562428614385299565013477 19980455365197243668440027)
        ·
          refine ⟨29970683047795865502660041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19980455365197243668440027 29970683047795865502660041)
          ·
            refine ⟨22478012285846899126995031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29970683047795865502660041 22478012285846899126995031)
            ·
              refine ⟨33717018428770348690492547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22478012285846899126995031 33717018428770348690492547)
              ·
                refine ⟨50575527643155523035738821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33717018428770348690492547 50575527643155523035738821)
                ·
                  refine ⟨9482911433091660569201029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50575527643155523035738821 9482911433091660569201029)
                  ·
                    refine ⟨1778045893704686356725193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9482911433091660569201029 1778045893704686356725193)
                    ·
                      refine ⟨1333534420278514767543895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778045893704686356725193 1333534420278514767543895)
                      ·
                        rfl

theorem cell23_2597049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_2597049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597049 prefixEnd_2597049 := by exact prefixLift 2597049
  have htrace : WordTrace (prefixWord ++ tailWord_2597049) baseStart_2597049 baseEnd_2597049 := by
    simpa [prefixWord, tailWord_2597049, baseEnd_2597049] using wordTrace_append hprefix tailTrace_2597049
  have hstable : (prefixWord ++ tailWord_2597049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597049).length < 2 ^ (prefixWord ++ tailWord_2597049).sum := by decide
  have hdescent : baseEnd_2597049 < baseStart_2597049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597093 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_2597093 : Nat := 118140960795 + 2597093 * 2 ^ 59
def prefixEnd_2597093 : Nat := 4983230072969 + 3 ^ 40 * 2597093 * 2
def baseEnd_2597093 : Nat := 444519004475770865131231

theorem tailTrace_2597093 : CollatzResearch.WordTrace tailWord_2597093 prefixEnd_2597093 444519004475770865131231 := by
  unfold tailWord_2597093
  simp only [CollatzResearch.WordTrace]
  refine ⟨94723763580183084016835933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63149175720122056011223955 94723763580183084016835933)
  ·
    refine ⟨35521411342568656506313475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94723763580183084016835933 35521411342568656506313475)
    ·
      refine ⟨53282117013852984759470213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35521411342568656506313475 53282117013852984759470213)
      ·
        refine ⟨9990396940097434642400665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53282117013852984759470213 9990396940097434642400665)
        ·
          refine ⟨7492797705073075981800499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9990396940097434642400665 7492797705073075981800499)
          ·
            refine ⟨11239196557609613972700749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7492797705073075981800499 11239196557609613972700749)
            ·
              refine ⟨4214698709103605239762781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11239196557609613972700749 4214698709103605239762781)
              ·
                refine ⟨1580512015913851964911043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4214698709103605239762781 1580512015913851964911043)
                ·
                  refine ⟨2370768023870777947366565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580512015913851964911043 2370768023870777947366565)
                  ·
                    refine ⟨444519004475770865131231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2370768023870777947366565 444519004475770865131231)
                    ·
                      rfl

theorem cell23_2597093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_2597093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597093 prefixEnd_2597093 := by exact prefixLift 2597093
  have htrace : WordTrace (prefixWord ++ tailWord_2597093) baseStart_2597093 baseEnd_2597093 := by
    simpa [prefixWord, tailWord_2597093, baseEnd_2597093] using wordTrace_append hprefix tailTrace_2597093
  have hstable : (prefixWord ++ tailWord_2597093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597093).length < 2 ^ (prefixWord ++ tailWord_2597093).sum := by decide
  have hdescent : baseEnd_2597093 < baseStart_2597093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597139 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 6, 2]
def baseStart_2597139 : Nat := 118140960795 + 2597139 * 2 ^ 59
def prefixEnd_2597139 : Nat := 4983230072969 + 3 ^ 40 * 2597139 * 2
def baseEnd_2597139 : Nat := 1333580633537419415418481

theorem tailTrace_2597139 : CollatzResearch.WordTrace tailWord_2597139 prefixEnd_2597139 1333580633537419415418481 := by
  unfold tailWord_2597139
  simp only [CollatzResearch.WordTrace]
  refine ⟨94725441338016433873010471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63150294225344289248673647 94725441338016433873010471)
  ·
    refine ⟨142088162007024650809515707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94725441338016433873010471 142088162007024650809515707)
    ·
      refine ⟨213132243010536976214273561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142088162007024650809515707 213132243010536976214273561)
      ·
        refine ⟨159849182257902732160705171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213132243010536976214273561 159849182257902732160705171)
        ·
          refine ⟨239773773386854098241057757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159849182257902732160705171 239773773386854098241057757)
          ·
            refine ⟨89915165020070286840396659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239773773386854098241057757 89915165020070286840396659)
            ·
              refine ⟨134872747530105430260594989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89915165020070286840396659 134872747530105430260594989)
              ·
                refine ⟨50577280323789536347723121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134872747530105430260594989 50577280323789536347723121)
                ·
                  refine ⟨37932960242842152260792341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50577280323789536347723121 37932960242842152260792341)
                  ·
                    refine ⟨1778107511383225887224641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37932960242842152260792341 1778107511383225887224641)
                    ·
                      refine ⟨1333580633537419415418481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778107511383225887224641 1333580633537419415418481)
                      ·
                        rfl

theorem cell23_2597139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6, 2].length) (baseStart_2597139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597139 prefixEnd_2597139 := by exact prefixLift 2597139
  have htrace : WordTrace (prefixWord ++ tailWord_2597139) baseStart_2597139 baseEnd_2597139 := by
    simpa [prefixWord, tailWord_2597139, baseEnd_2597139] using wordTrace_append hprefix tailTrace_2597139
  have hstable : (prefixWord ++ tailWord_2597139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597139).length < 2 ^ (prefixWord ++ tailWord_2597139).sum := by decide
  have hdescent : baseEnd_2597139 < baseStart_2597139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597143 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 2, 3, 2]
def baseStart_2597143 : Nat := 118140960795 + 2597143 * 2 ^ 59
def prefixEnd_2597143 : Nat := 4983230072969 + 3 ^ 40 * 2597143 * 2
def baseEnd_2597143 : Nat := 1333582687460037399768463

theorem tailTrace_2597143 : CollatzResearch.WordTrace tailWord_2597143 prefixEnd_2597143 1333582687460037399768463 := by
  unfold tailWord_2597143
  simp only [CollatzResearch.WordTrace]
  refine ⟨94725587230001942556156083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63150391486667961704104055 94725587230001942556156083)
  ·
    refine ⟨142088380845002913834234125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94725587230001942556156083 142088380845002913834234125)
    ·
      refine ⟨53283142816876092687837797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142088380845002913834234125 53283142816876092687837797)
      ·
        refine ⟨9990589278164267378969587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53283142816876092687837797 9990589278164267378969587)
        ·
          refine ⟨14985883917246401068454381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990589278164267378969587 14985883917246401068454381)
          ·
            refine ⟨5619706468967400400670393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14985883917246401068454381 5619706468967400400670393)
            ·
              refine ⟨4214779851725550300502795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5619706468967400400670393 4214779851725550300502795)
              ·
                refine ⟨6322169777588325450754193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214779851725550300502795 6322169777588325450754193)
                ·
                  refine ⟨4741627333191244088065645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6322169777588325450754193 4741627333191244088065645)
                  ·
                    refine ⟨1778110249946716533024617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4741627333191244088065645 1778110249946716533024617)
                    ·
                      refine ⟨1333582687460037399768463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778110249946716533024617 1333582687460037399768463)
                      ·
                        rfl

theorem cell23_2597143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_2597143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597143 prefixEnd_2597143 := by exact prefixLift 2597143
  have htrace : WordTrace (prefixWord ++ tailWord_2597143) baseStart_2597143 baseEnd_2597143 := by
    simpa [prefixWord, tailWord_2597143, baseEnd_2597143] using wordTrace_append hprefix tailTrace_2597143
  have hstable : (prefixWord ++ tailWord_2597143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597143).length < 2 ^ (prefixWord ++ tailWord_2597143).sum := by decide
  have hdescent : baseEnd_2597143 < baseStart_2597143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597173 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_2597173 : Nat := 118140960795 + 2597173 * 2 ^ 59
def prefixEnd_2597173 : Nat := 4983230072969 + 3 ^ 40 * 2597173 * 2
def baseEnd_2597173 : Nat := 1333598091879672282393325

theorem tailTrace_2597173 : CollatzResearch.WordTrace tailWord_2597173 prefixEnd_2597173 1333598091879672282393325 := by
  unfold tailWord_2597173
  simp only [CollatzResearch.WordTrace]
  refine ⟨94726681419893257679748173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63151120946595505119832115 94726681419893257679748173)
  ·
    refine ⟨35522505532459971629905565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94726681419893257679748173 35522505532459971629905565)
    ·
      refine ⟨13320939574672489361214587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35522505532459971629905565 13320939574672489361214587)
      ·
        refine ⟨19981409362008734041821881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13320939574672489361214587 19981409362008734041821881)
        ·
          refine ⟨14986057021506550531366411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19981409362008734041821881 14986057021506550531366411)
          ·
            refine ⟨22479085532259825797049617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14986057021506550531366411 22479085532259825797049617)
            ·
              refine ⟨16859314149194869347787213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22479085532259825797049617 16859314149194869347787213)
              ·
                refine ⟨6322242805948076005420205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16859314149194869347787213 6322242805948076005420205)
                ·
                  refine ⟨2370841052230528502032577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6322242805948076005420205 2370841052230528502032577)
                  ·
                    refine ⟨1778130789172896376524433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2370841052230528502032577 1778130789172896376524433)
                    ·
                      refine ⟨1333598091879672282393325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778130789172896376524433 1333598091879672282393325)
                      ·
                        rfl

theorem cell23_2597173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_2597173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597173 prefixEnd_2597173 := by exact prefixLift 2597173
  have htrace : WordTrace (prefixWord ++ tailWord_2597173) baseStart_2597173 baseEnd_2597173 := by
    simpa [prefixWord, tailWord_2597173, baseEnd_2597173] using wordTrace_append hprefix tailTrace_2597173
  have hstable : (prefixWord ++ tailWord_2597173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597173).length < 2 ^ (prefixWord ++ tailWord_2597173).sum := by decide
  have hdescent : baseEnd_2597173 < baseStart_2597173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597223 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2597223 : Nat := 118140960795 + 2597223 * 2 ^ 59
def prefixEnd_2597223 : Nat := 4983230072969 + 3 ^ 40 * 2597223 * 2
def baseEnd_2597223 : Nat := 1333623765912397086768095

theorem tailTrace_2597223 : CollatzResearch.WordTrace tailWord_2597223 prefixEnd_2597223 1333623765912397086768095 := by
  unfold tailWord_2597223
  simp only [CollatzResearch.WordTrace]
  refine ⟨94728505069712116219068323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63152336713141410812712215 94728505069712116219068323)
  ·
    refine ⟨142092757604568174328602485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94728505069712116219068323 142092757604568174328602485)
    ·
      refine ⟨13321196025428266343306483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142092757604568174328602485 13321196025428266343306483)
      ·
        refine ⟨19981794038142399514959725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13321196025428266343306483 19981794038142399514959725)
        ·
          refine ⟨7493172764303399818109897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19981794038142399514959725 7493172764303399818109897)
          ·
            refine ⟨5619879573227549863582423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7493172764303399818109897 5619879573227549863582423)
            ·
              refine ⟨8429819359841324795373635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619879573227549863582423 8429819359841324795373635)
              ·
                refine ⟨12644729039761987193060453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8429819359841324795373635 12644729039761987193060453)
                ·
                  refine ⟨2370886694955372598698835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12644729039761987193060453 2370886694955372598698835)
                  ·
                    refine ⟨3556330042433058898048253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2370886694955372598698835 3556330042433058898048253)
                    ·
                      refine ⟨1333623765912397086768095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3556330042433058898048253 1333623765912397086768095)
                      ·
                        rfl

theorem cell23_2597223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2597223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597223 prefixEnd_2597223 := by exact prefixLift 2597223
  have htrace : WordTrace (prefixWord ++ tailWord_2597223) baseStart_2597223 baseEnd_2597223 := by
    simpa [prefixWord, tailWord_2597223, baseEnd_2597223] using wordTrace_append hprefix tailTrace_2597223
  have hstable : (prefixWord ++ tailWord_2597223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597223).length < 2 ^ (prefixWord ++ tailWord_2597223).sum := by decide
  have hdescent : baseEnd_2597223 < baseStart_2597223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597279 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2597279 : Nat := 118140960795 + 2597279 * 2 ^ 59
def prefixEnd_2597279 : Nat := 4983230072969 + 3 ^ 40 * 2597279 * 2
def baseEnd_2597279 : Nat := 1333652520829048867667837

theorem tailTrace_2597279 : CollatzResearch.WordTrace tailWord_2597279 prefixEnd_2597279 1333652520829048867667837 := by
  unfold tailWord_2597279
  simp only [CollatzResearch.WordTrace]
  refine ⟨94730547557509237783106891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63153698371672825188737927 94730547557509237783106891)
  ·
    refine ⟨142095821336263856674660337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94730547557509237783106891 142095821336263856674660337)
    ·
      refine ⟨106571866002197892505995253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142095821336263856674660337 106571866002197892505995253)
      ·
        refine ⟨9991112437706052422437055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106571866002197892505995253 9991112437706052422437055)
        ·
          refine ⟨14986668656559078633655583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9991112437706052422437055 14986668656559078633655583)
          ·
            refine ⟨22480002984838617950483375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14986668656559078633655583 22480002984838617950483375)
            ·
              refine ⟨33720004477257926925725063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22480002984838617950483375 33720004477257926925725063)
              ·
                refine ⟨50580006715886890388587595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33720004477257926925725063 50580006715886890388587595)
                ·
                  refine ⟨75870010073830335582881393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50580006715886890388587595 75870010073830335582881393)
                  ·
                    refine ⟨56902507555372751687161045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75870010073830335582881393 56902507555372751687161045)
                    ·
                      refine ⟨1333652520829048867667837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56902507555372751687161045 1333652520829048867667837)
                      ·
                        rfl

theorem cell23_2597279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2597279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597279 prefixEnd_2597279 := by exact prefixLift 2597279
  have htrace : WordTrace (prefixWord ++ tailWord_2597279) baseStart_2597279 baseEnd_2597279 := by
    simpa [prefixWord, tailWord_2597279, baseEnd_2597279] using wordTrace_append hprefix tailTrace_2597279
  have hstable : (prefixWord ++ tailWord_2597279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597279).length < 2 ^ (prefixWord ++ tailWord_2597279).sum := by decide
  have hdescent : baseEnd_2597279 < baseStart_2597279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597297 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 2, 2, 2]
def baseStart_2597297 : Nat := 118140960795 + 2597297 * 2 ^ 59
def prefixEnd_2597297 : Nat := 4983230072969 + 3 ^ 40 * 2597297 * 2
def baseEnd_2597297 : Nat := 1333661763480829797242755

theorem tailTrace_2597297 : CollatzResearch.WordTrace tailWord_2597297 prefixEnd_2597297 1333661763480829797242755 := by
  unfold tailWord_2597297
  simp only [CollatzResearch.WordTrace]
  refine ⟨94731204071444026857262145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63154136047629351238174763 94731204071444026857262145)
  ·
    refine ⟨71048403053583020142946609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94731204071444026857262145 71048403053583020142946609)
    ·
      refine ⟨53286302290187265107209957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71048403053583020142946609 53286302290187265107209957)
      ·
        refine ⟨9991181679410112207601867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53286302290187265107209957 9991181679410112207601867)
        ·
          refine ⟨14986772519115168311402801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9991181679410112207601867 14986772519115168311402801)
          ·
            refine ⟨11240079389336376233552101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14986772519115168311402801 11240079389336376233552101)
            ·
              refine ⟨2107514885500570543791019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11240079389336376233552101 2107514885500570543791019)
              ·
                refine ⟨3161272328250855815686529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107514885500570543791019 3161272328250855815686529)
                ·
                  refine ⟨2370954246188141861764897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161272328250855815686529 2370954246188141861764897)
                  ·
                    refine ⟨1778215684641106396323673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2370954246188141861764897 1778215684641106396323673)
                    ·
                      refine ⟨1333661763480829797242755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778215684641106396323673 1333661763480829797242755)
                      ·
                        rfl

theorem cell23_2597297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_2597297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597297 prefixEnd_2597297 := by exact prefixLift 2597297
  have htrace : WordTrace (prefixWord ++ tailWord_2597297) baseStart_2597297 baseEnd_2597297 := by
    simpa [prefixWord, tailWord_2597297, baseEnd_2597297] using wordTrace_append hprefix tailTrace_2597297
  have hstable : (prefixWord ++ tailWord_2597297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597297).length < 2 ^ (prefixWord ++ tailWord_2597297).sum := by decide
  have hdescent : baseEnd_2597297 < baseStart_2597297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597356 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_2597356 : Nat := 118140960795 + 2597356 * 2 ^ 59
def prefixEnd_2597356 : Nat := 4983230072969 + 3 ^ 40 * 2597356 * 2
def baseEnd_2597356 : Nat := 1333692058839445066404983

theorem tailTrace_2597356 : CollatzResearch.WordTrace tailWord_2597356 prefixEnd_2597356 1333692058839445066404983 := by
  unfold tailWord_2597356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47366677989115139966829961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63155570652153519955773281 47366677989115139966829961)
  ·
    refine ⟨35525008491836354975122471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47366677989115139966829961 35525008491836354975122471)
    ·
      refine ⟨53287512737754532462683707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35525008491836354975122471 53287512737754532462683707)
      ·
        refine ⟨79931269106631798694025561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53287512737754532462683707 79931269106631798694025561)
        ·
          refine ⟨59948451829973849020519171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79931269106631798694025561 59948451829973849020519171)
          ·
            refine ⟨89922677744960773530778757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59948451829973849020519171 89922677744960773530778757)
            ·
              refine ⟨16860502077180145037021017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89922677744960773530778757 16860502077180145037021017)
              ·
                refine ⟨12645376557885108777765763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16860502077180145037021017 12645376557885108777765763)
                ·
                  refine ⟨18968064836827663166648645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12645376557885108777765763 18968064836827663166648645)
                  ·
                    refine ⟨3556512156905186843746621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18968064836827663166648645 3556512156905186843746621)
                    ·
                      refine ⟨1333692058839445066404983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3556512156905186843746621 1333692058839445066404983)
                      ·
                        rfl

theorem cell23_2597356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_2597356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597356 prefixEnd_2597356 := by exact prefixLift 2597356
  have htrace : WordTrace (prefixWord ++ tailWord_2597356) baseStart_2597356 baseEnd_2597356 := by
    simpa [prefixWord, tailWord_2597356, baseEnd_2597356] using wordTrace_append hprefix tailTrace_2597356
  have hstable : (prefixWord ++ tailWord_2597356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597356).length < 2 ^ (prefixWord ++ tailWord_2597356).sum := by decide
  have hdescent : baseEnd_2597356 < baseStart_2597356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597359 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 10]
def baseStart_2597359 : Nat := 118140960795 + 2597359 * 2 ^ 59
def prefixEnd_2597359 : Nat := 4983230072969 + 3 ^ 40 * 2597359 * 2
def baseEnd_2597359 : Nat := 148188177697934283851941

theorem tailTrace_2597359 : CollatzResearch.WordTrace tailWord_2597359 prefixEnd_2597359 148188177697934283851941 := by
  unfold tailWord_2597359
  simp only [CollatzResearch.WordTrace]
  refine ⟨94733465397219411446019131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63155643598146274297346087 94733465397219411446019131)
  ·
    refine ⟨142100198095829117169028697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94733465397219411446019131 142100198095829117169028697)
    ·
      refine ⟨106575148571871837876771523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142100198095829117169028697 106575148571871837876771523)
      ·
        refine ⟨159862722857807756815157285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106575148571871837876771523 159862722857807756815157285)
        ·
          refine ⟨29974260535838954402841991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159862722857807756815157285 29974260535838954402841991)
          ·
            refine ⟨44961390803758431604262987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29974260535838954402841991 44961390803758431604262987)
            ·
              refine ⟨67442086205637647406394481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44961390803758431604262987 67442086205637647406394481)
              ·
                refine ⟨50581564654228235554795861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67442086205637647406394481 50581564654228235554795861)
                ·
                  refine ⟨148188177697934283851941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50581564654228235554795861 148188177697934283851941)
                  ·
                    rfl

theorem cell23_2597359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 10].length) (baseStart_2597359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597359 prefixEnd_2597359 := by exact prefixLift 2597359
  have htrace : WordTrace (prefixWord ++ tailWord_2597359) baseStart_2597359 baseEnd_2597359 := by
    simpa [prefixWord, tailWord_2597359, baseEnd_2597359] using wordTrace_append hprefix tailTrace_2597359
  have hstable : (prefixWord ++ tailWord_2597359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597359).length < 2 ^ (prefixWord ++ tailWord_2597359).sum := by decide
  have hdescent : baseEnd_2597359 < baseStart_2597359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597413 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 1, 5, 2]
def baseStart_2597413 : Nat := 118140960795 + 2597413 * 2 ^ 59
def prefixEnd_2597413 : Nat := 4983230072969 + 3 ^ 40 * 2597413 * 2
def baseEnd_2597413 : Nat := 1333721327236751343392221

theorem tailTrace_2597413 : CollatzResearch.WordTrace tailWord_2597413 prefixEnd_2597413 1333721327236751343392221 := by
  unfold tailWord_2597413
  simp only [CollatzResearch.WordTrace]
  refine ⟨94735434939023778668484893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63156956626015852445656595 94735434939023778668484893)
  ·
    refine ⟨35525788102133917000681835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94735434939023778668484893 35525788102133917000681835)
    ·
      refine ⟨53288682153200875501022753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35525788102133917000681835 53288682153200875501022753)
      ·
        refine ⟨39966511614900656625767065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53288682153200875501022753 39966511614900656625767065)
        ·
          refine ⟨29974883711175492469325299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39966511614900656625767065 29974883711175492469325299)
          ·
            refine ⟨44962325566763238703987949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29974883711175492469325299 44962325566763238703987949)
            ·
              refine ⟨16860872087536214513995481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44962325566763238703987949 16860872087536214513995481)
              ·
                refine ⟨12645654065652160885496611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16860872087536214513995481 12645654065652160885496611)
                ·
                  refine ⟨18968481098478241328244917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12645654065652160885496611 18968481098478241328244917)
                  ·
                    refine ⟨1778295102982335124522961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18968481098478241328244917 1778295102982335124522961)
                    ·
                      refine ⟨1333721327236751343392221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778295102982335124522961 1333721327236751343392221)
                      ·
                        rfl

theorem cell23_2597413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_2597413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597413 prefixEnd_2597413 := by exact prefixLift 2597413
  have htrace : WordTrace (prefixWord ++ tailWord_2597413) baseStart_2597413 baseEnd_2597413 := by
    simpa [prefixWord, tailWord_2597413, baseEnd_2597413] using wordTrace_append hprefix tailTrace_2597413
  have hstable : (prefixWord ++ tailWord_2597413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597413).length < 2 ^ (prefixWord ++ tailWord_2597413).sum := by decide
  have hdescent : baseEnd_2597413 < baseStart_2597413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597456 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_2597456 : Nat := 118140960795 + 2597456 * 2 ^ 59
def prefixEnd_2597456 : Nat := 4983230072969 + 3 ^ 40 * 2597456 * 2
def baseEnd_2597456 : Nat := 1333743406904894675154523

theorem tailTrace_2597456 : CollatzResearch.WordTrace tailWord_2597456 prefixEnd_2597456 1333743406904894675154523 := by
  unfold tailWord_2597456
  simp only [CollatzResearch.WordTrace]
  refine ⟨47368501638933998506150111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63158002185245331341533481 47368501638933998506150111)
  ·
    refine ⟨71052752458400997759225167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47368501638933998506150111 71052752458400997759225167)
    ·
      refine ⟨106579128687601496638837751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71052752458400997759225167 106579128687601496638837751)
      ·
        refine ⟨159868693031402244958256627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106579128687601496638837751 159868693031402244958256627)
        ·
          refine ⟨239803039547103367437384941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159868693031402244958256627 239803039547103367437384941)
          ·
            refine ⟨89926139830163762789019353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239803039547103367437384941 89926139830163762789019353)
            ·
              refine ⟨67444604872622822091764515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89926139830163762789019353 67444604872622822091764515)
              ·
                refine ⟨101166907308934233137646773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67444604872622822091764515 101166907308934233137646773)
                ·
                  refine ⟨9484397560212584356654385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101166907308934233137646773 9484397560212584356654385)
                  ·
                    refine ⟨7113298170159438267490789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9484397560212584356654385 7113298170159438267490789)
                    ·
                      refine ⟨1333743406904894675154523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7113298170159438267490789 1333743406904894675154523)
                      ·
                        rfl

theorem cell23_2597456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_2597456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597456 prefixEnd_2597456 := by exact prefixLift 2597456
  have htrace : WordTrace (prefixWord ++ tailWord_2597456) baseStart_2597456 baseEnd_2597456 := by
    simpa [prefixWord, tailWord_2597456, baseEnd_2597456] using wordTrace_append hprefix tailTrace_2597456
  have hstable : (prefixWord ++ tailWord_2597456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597456).length < 2 ^ (prefixWord ++ tailWord_2597456).sum := by decide
  have hdescent : baseEnd_2597456 < baseStart_2597456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597463 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_2597463 : Nat := 118140960795 + 2597463 * 2 ^ 59
def prefixEnd_2597463 : Nat := 4983230072969 + 3 ^ 40 * 2597463 * 2
def baseEnd_2597463 : Nat := 1333747001269476147766991

theorem tailTrace_2597463 : CollatzResearch.WordTrace tailWord_2597463 prefixEnd_2597463 1333747001269476147766991 := by
  unfold tailWord_2597463
  simp only [CollatzResearch.WordTrace]
  refine ⟨94737258588842637207805043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63158172392561758138536695 94737258588842637207805043)
  ·
    refine ⟨142105887883263955811707565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94737258588842637207805043 142105887883263955811707565)
    ·
      refine ⟨53289707956223983429390337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142105887883263955811707565 53289707956223983429390337)
      ·
        refine ⟨39967280967167987572042753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53289707956223983429390337 39967280967167987572042753)
        ·
          refine ⟨29975460725375990679032065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39967280967167987572042753 29975460725375990679032065)
          ·
            refine ⟨22481595544031993009274049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29975460725375990679032065 22481595544031993009274049)
            ·
              refine ⟨16861196658023994756955537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22481595544031993009274049 16861196658023994756955537)
              ·
                refine ⟨12645897493517996067716653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16861196658023994756955537 12645897493517996067716653)
                ·
                  refine ⟨4742211560069248525393745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12645897493517996067716653 4742211560069248525393745)
                  ·
                    refine ⟨3556658670051936394045309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4742211560069248525393745 3556658670051936394045309)
                    ·
                      refine ⟨1333747001269476147766991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3556658670051936394045309 1333747001269476147766991)
                      ·
                        rfl

theorem cell23_2597463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_2597463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597463 prefixEnd_2597463 := by exact prefixLift 2597463
  have htrace : WordTrace (prefixWord ++ tailWord_2597463) baseStart_2597463 baseEnd_2597463 := by
    simpa [prefixWord, tailWord_2597463, baseEnd_2597463] using wordTrace_append hprefix tailTrace_2597463
  have hstable : (prefixWord ++ tailWord_2597463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597463).length < 2 ^ (prefixWord ++ tailWord_2597463).sum := by decide
  have hdescent : baseEnd_2597463 < baseStart_2597463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597474 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2597474 : Nat := 118140960795 + 2597474 * 2 ^ 59
def prefixEnd_2597474 : Nat := 4983230072969 + 3 ^ 40 * 2597474 * 2
def baseEnd_2597474 : Nat := 444584216518891868243147

theorem tailTrace_2597474 : CollatzResearch.WordTrace tailWord_2597474 prefixEnd_2597474 444584216518891868243147 := by
  unfold tailWord_2597474
  simp only [CollatzResearch.WordTrace]
  refine ⟨23684414947950696521613869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63158439861201857390970317 23684414947950696521613869)
  ·
    refine ⟨8881655605481511195605201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23684414947950696521613869 8881655605481511195605201)
    ·
      refine ⟨6661241704111133396703901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8881655605481511195605201 6661241704111133396703901)
      ·
        refine ⟨2497965639041675023763963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6661241704111133396703901 2497965639041675023763963)
        ·
          refine ⟨3746948458562512535645945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2497965639041675023763963 3746948458562512535645945)
          ·
            refine ⟨2810211343921884401734459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746948458562512535645945 2810211343921884401734459)
            ·
              refine ⟨4215317015882826602601689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810211343921884401734459 4215317015882826602601689)
              ·
                refine ⟨3161487761912119951951267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215317015882826602601689 3161487761912119951951267)
                ·
                  refine ⟨4742231642868179927926901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161487761912119951951267 4742231642868179927926901)
                  ·
                    refine ⟨444584216518891868243147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4742231642868179927926901 444584216518891868243147)
                    ·
                      rfl

theorem cell23_2597474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2597474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597474 prefixEnd_2597474 := by exact prefixLift 2597474
  have htrace : WordTrace (prefixWord ++ tailWord_2597474) baseStart_2597474 baseEnd_2597474 := by
    simpa [prefixWord, tailWord_2597474, baseEnd_2597474] using wordTrace_append hprefix tailTrace_2597474
  have hstable : (prefixWord ++ tailWord_2597474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597474).length < 2 ^ (prefixWord ++ tailWord_2597474).sum := by decide
  have hdescent : baseEnd_2597474 < baseStart_2597474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597477 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_2597477 : Nat := 118140960795 + 2597477 * 2 ^ 59
def prefixEnd_2597477 : Nat := 4983230072969 + 3 ^ 40 * 2597477 * 2
def baseEnd_2597477 : Nat := 1333754189998639092991927

theorem tailTrace_2597477 : CollatzResearch.WordTrace tailWord_2597477 prefixEnd_2597477 1333754189998639092991927 := by
  unfold tailWord_2597477
  simp only [CollatzResearch.WordTrace]
  refine ⟨94737769210791917598814685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63158512807194611732543123 94737769210791917598814685)
  ·
    refine ⟨35526663454046969099555507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94737769210791917598814685 35526663454046969099555507)
    ·
      refine ⟨53289995181070453649333261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35526663454046969099555507 53289995181070453649333261)
      ·
        refine ⟨19983748192901420118499973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53289995181070453649333261 19983748192901420118499973)
        ·
          refine ⟨3746952786169016272218745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19983748192901420118499973 3746952786169016272218745)
          ·
            refine ⟨2810214589626762204164059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746952786169016272218745 2810214589626762204164059)
            ·
              refine ⟨4215321884440143306246089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810214589626762204164059 4215321884440143306246089)
              ·
                refine ⟨3161491413330107479684567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215321884440143306246089 3161491413330107479684567)
                ·
                  refine ⟨4742237119995161219526851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161491413330107479684567 4742237119995161219526851)
                  ·
                    refine ⟨7113355679992741829290277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4742237119995161219526851 7113355679992741829290277)
                    ·
                      refine ⟨1333754189998639092991927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7113355679992741829290277 1333754189998639092991927)
                      ·
                        rfl

theorem cell23_2597477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_2597477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597477 prefixEnd_2597477 := by exact prefixLift 2597477
  have htrace : WordTrace (prefixWord ++ tailWord_2597477) baseStart_2597477 baseEnd_2597477 := by
    simpa [prefixWord, tailWord_2597477, baseEnd_2597477] using wordTrace_append hprefix tailTrace_2597477
  have hstable : (prefixWord ++ tailWord_2597477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597477).length < 2 ^ (prefixWord ++ tailWord_2597477).sum := by decide
  have hdescent : baseEnd_2597477 < baseStart_2597477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597490 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2597490 : Nat := 118140960795 + 2597490 * 2 ^ 59
def prefixEnd_2597490 : Nat := 4983230072969 + 3 ^ 40 * 2597490 * 2
def baseEnd_2597490 : Nat := 1333760865247147542129367

theorem tailTrace_2597490 : CollatzResearch.WordTrace tailWord_2597490 prefixEnd_2597490 1333760865247147542129367 := by
  unfold tailWord_2597490
  simp only [CollatzResearch.WordTrace]
  refine ⟨23684560839936205204759481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63158828906496547212691949 23684560839936205204759481)
  ·
    refine ⟨17763420629952153903569611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23684560839936205204759481 17763420629952153903569611)
    ·
      refine ⟨26645130944928230855354417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17763420629952153903569611 26645130944928230855354417)
      ·
        refine ⟨19983848208696173141515813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26645130944928230855354417 19983848208696173141515813)
        ·
          refine ⟨3746971539130532464034215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19983848208696173141515813 3746971539130532464034215)
          ·
            refine ⟨5620457308695798696051323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746971539130532464034215 5620457308695798696051323)
            ·
              refine ⟨8430685963043698044076985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620457308695798696051323 8430685963043698044076985)
              ·
                refine ⟨6323014472282773533057739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8430685963043698044076985 6323014472282773533057739)
                ·
                  refine ⟨9484521708424160299586609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6323014472282773533057739 9484521708424160299586609)
                  ·
                    refine ⟨7113391281318120224689957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9484521708424160299586609 7113391281318120224689957)
                    ·
                      refine ⟨1333760865247147542129367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7113391281318120224689957 1333760865247147542129367)
                      ·
                        rfl

theorem cell23_2597490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2597490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597490 prefixEnd_2597490 := by exact prefixLift 2597490
  have htrace : WordTrace (prefixWord ++ tailWord_2597490) baseStart_2597490 baseEnd_2597490 := by
    simpa [prefixWord, tailWord_2597490, baseEnd_2597490] using wordTrace_append hprefix tailTrace_2597490
  have hstable : (prefixWord ++ tailWord_2597490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597490).length < 2 ^ (prefixWord ++ tailWord_2597490).sum := by decide
  have hdescent : baseEnd_2597490 < baseStart_2597490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597494 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2597494 : Nat := 118140960795 + 2597494 * 2 ^ 59
def prefixEnd_2597494 : Nat := 4983230072969 + 3 ^ 40 * 2597494 * 2
def baseEnd_2597494 : Nat := 1333762919169765526479349

theorem tailTrace_2597494 : CollatzResearch.WordTrace tailWord_2597494 prefixEnd_2597494 1333762919169765526479349 := by
  unfold tailWord_2597494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921149328233145593886471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63158926167820219668122357 5921149328233145593886471)
  ·
    refine ⟨8881723992349718390829707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921149328233145593886471 8881723992349718390829707)
    ·
      refine ⟨13322585988524577586244561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8881723992349718390829707 13322585988524577586244561)
      ·
        refine ⟨9991939491393433189683421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13322585988524577586244561 9991939491393433189683421)
        ·
          refine ⟨3746977309272537446131283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9991939491393433189683421 3746977309272537446131283)
          ·
            refine ⟨5620465963908806169196925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746977309272537446131283 5620465963908806169196925)
            ·
              refine ⟨2107674736465802313448847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5620465963908806169196925 2107674736465802313448847)
              ·
                refine ⟨3161512104698703470173271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107674736465802313448847 3161512104698703470173271)
                ·
                  refine ⟨4742268157048055205259907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161512104698703470173271 4742268157048055205259907)
                  ·
                    refine ⟨7113402235572082807889861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4742268157048055205259907 7113402235572082807889861)
                    ·
                      refine ⟨1333762919169765526479349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7113402235572082807889861 1333762919169765526479349)
                      ·
                        rfl

theorem cell23_2597494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2597494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597494 prefixEnd_2597494 := by exact prefixLift 2597494
  have htrace : WordTrace (prefixWord ++ tailWord_2597494) baseStart_2597494 baseEnd_2597494 := by
    simpa [prefixWord, tailWord_2597494, baseEnd_2597494] using wordTrace_append hprefix tailTrace_2597494
  have hstable : (prefixWord ++ tailWord_2597494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597494).length < 2 ^ (prefixWord ++ tailWord_2597494).sum := by decide
  have hdescent : baseEnd_2597494 < baseStart_2597494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597497 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 1, 2, 3]
def baseStart_2597497 : Nat := 118140960795 + 2597497 * 2 ^ 59
def prefixEnd_2597497 : Nat := 4983230072969 + 3 ^ 40 * 2597497 * 2
def baseEnd_2597497 : Nat := 1333764459611729014741835

theorem tailTrace_2597497 : CollatzResearch.WordTrace tailWord_2597497 prefixEnd_2597497 1333764459611729014741835 := by
  unfold tailWord_2597497
  simp only [CollatzResearch.WordTrace]
  refine ⟨94738498670719461014542745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63158999113812974009695163 94738498670719461014542745)
  ·
    refine ⟨71053874003039595760907059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94738498670719461014542745 71053874003039595760907059)
    ·
      refine ⟨106580811004559393641360589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71053874003039595760907059 106580811004559393641360589)
      ·
        refine ⟨39967804126709772615510221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106580811004559393641360589 39967804126709772615510221)
        ·
          refine ⟨14987926547516164730816333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39967804126709772615510221 14987926547516164730816333)
          ·
            refine ⟨5620472455318561774056125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14987926547516164730816333 5620472455318561774056125)
            ·
              refine ⟨2107677170744460665271047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5620472455318561774056125 2107677170744460665271047)
              ·
                refine ⟨3161515756116690997906571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107677170744460665271047 3161515756116690997906571)
                ·
                  refine ⟨4742273634175036496859857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161515756116690997906571 4742273634175036496859857)
                  ·
                    refine ⟨3556705225631277372644893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4742273634175036496859857 3556705225631277372644893)
                    ·
                      refine ⟨1333764459611729014741835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3556705225631277372644893 1333764459611729014741835)
                      ·
                        rfl

theorem cell23_2597497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_2597497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597497 prefixEnd_2597497 := by exact prefixLift 2597497
  have htrace : WordTrace (prefixWord ++ tailWord_2597497) baseStart_2597497 baseEnd_2597497 := by
    simpa [prefixWord, tailWord_2597497, baseEnd_2597497] using wordTrace_append hprefix tailTrace_2597497
  have hstable : (prefixWord ++ tailWord_2597497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597497).length < 2 ^ (prefixWord ++ tailWord_2597497).sum := by decide
  have hdescent : baseEnd_2597497 < baseStart_2597497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597567 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 4, 2, 2]
def baseStart_2597567 : Nat := 118140960795 + 2597567 * 2 ^ 59
def prefixEnd_2597567 : Nat := 4983230072969 + 3 ^ 40 * 2597567 * 2
def baseEnd_2597567 : Nat := 1333800403257543740866513

theorem tailTrace_2597567 : CollatzResearch.WordTrace tailWord_2597567 prefixEnd_2597567 1333800403257543740866513 := by
  unfold tailWord_2597567
  simp only [CollatzResearch.WordTrace]
  refine ⟨94741051780465862969590955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63160701186977241979727303 94741051780465862969590955)
  ·
    refine ⟨142111577670698794454386433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94741051780465862969590955 142111577670698794454386433)
    ·
      refine ⟨106583683253024095840789825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142111577670698794454386433 106583683253024095840789825)
      ·
        refine ⟨79937762439768071880592369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106583683253024095840789825 79937762439768071880592369)
        ·
          refine ⟨59953321829826053910444277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79937762439768071880592369 59953321829826053910444277)
          ·
            refine ⟨5620623921546192554104151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59953321829826053910444277 5620623921546192554104151)
            ·
              refine ⟨8430935882319288831156227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620623921546192554104151 8430935882319288831156227)
              ·
                refine ⟨12646403823478933246734341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430935882319288831156227 12646403823478933246734341)
                ·
                  refine ⟨2371200716902299983762689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12646403823478933246734341 2371200716902299983762689)
                  ·
                    refine ⟨1778400537676724987822017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2371200716902299983762689 1778400537676724987822017)
                    ·
                      refine ⟨1333800403257543740866513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778400537676724987822017 1333800403257543740866513)
                      ·
                        rfl

theorem cell23_2597567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_2597567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597567 prefixEnd_2597567 := by exact prefixLift 2597567
  have htrace : WordTrace (prefixWord ++ tailWord_2597567) baseStart_2597567 baseEnd_2597567 := by
    simpa [prefixWord, tailWord_2597567, baseEnd_2597567] using wordTrace_append hprefix tailTrace_2597567
  have hstable : (prefixWord ++ tailWord_2597567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597567).length < 2 ^ (prefixWord ++ tailWord_2597567).sum := by decide
  have hdescent : baseEnd_2597567 < baseStart_2597567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597580 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2597580 : Nat := 118140960795 + 2597580 * 2 ^ 59
def prefixEnd_2597580 : Nat := 4983230072969 + 3 ^ 40 * 2597580 * 2
def baseEnd_2597580 : Nat := 1333807078506052190003953

theorem tailTrace_2597580 : CollatzResearch.WordTrace tailWord_2597580 prefixEnd_2597580 1333807078506052190003953 := by
  unfold tailWord_2597580
  simp only [CollatzResearch.WordTrace]
  refine ⟨47370762964709383094907097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63161017286279177459876129 47370762964709383094907097)
  ·
    refine ⟨35528072223532037321180323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47370762964709383094907097 35528072223532037321180323)
    ·
      refine ⟨53292108335298055981770485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35528072223532037321180323 53292108335298055981770485)
      ·
        refine ⟨4996135156434192748290983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53292108335298055981770485 4996135156434192748290983)
        ·
          refine ⟨7494202734651289122436475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4996135156434192748290983 7494202734651289122436475)
          ·
            refine ⟨11241304101976933683654713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494202734651289122436475 11241304101976933683654713)
            ·
              refine ⟨8430978076482700262741035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11241304101976933683654713 8430978076482700262741035)
              ·
                refine ⟨12646467114724050394111553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430978076482700262741035 12646467114724050394111553)
                ·
                  refine ⟨9484850336043037795583665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12646467114724050394111553 9484850336043037795583665)
                  ·
                    refine ⟨7113637752032278346687749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9484850336043037795583665 7113637752032278346687749)
                    ·
                      refine ⟨1333807078506052190003953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7113637752032278346687749 1333807078506052190003953)
                      ·
                        rfl

theorem cell23_2597580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2597580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597580 prefixEnd_2597580 := by exact prefixLift 2597580
  have htrace : WordTrace (prefixWord ++ tailWord_2597580) baseStart_2597580 baseEnd_2597580 := by
    simpa [prefixWord, tailWord_2597580, baseEnd_2597580] using wordTrace_append hprefix tailTrace_2597580
  have hstable : (prefixWord ++ tailWord_2597580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597580).length < 2 ^ (prefixWord ++ tailWord_2597580).sum := by decide
  have hdescent : baseEnd_2597580 < baseStart_2597580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597610 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_2597610 : Nat := 118140960795 + 2597610 * 2 ^ 59
def prefixEnd_2597610 : Nat := 4983230072969 + 3 ^ 40 * 2597610 * 2
def baseEnd_2597610 : Nat := 1333822482925687072628815

theorem tailTrace_2597610 : CollatzResearch.WordTrace tailWord_2597610 prefixEnd_2597610 1333822482925687072628815 := by
  unfold tailWord_2597610
  simp only [CollatzResearch.WordTrace]
  refine ⟨23685655029827520328351571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63161746746206720875604189 23685655029827520328351571)
  ·
    refine ⟨35528482544741280492527357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23685655029827520328351571 35528482544741280492527357)
    ·
      refine ⟨13323180954277980184697759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35528482544741280492527357 13323180954277980184697759)
      ·
        refine ⟨19984771431416970277046639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13323180954277980184697759 19984771431416970277046639)
        ·
          refine ⟨29977157147125455415569959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19984771431416970277046639 29977157147125455415569959)
          ·
            refine ⟨44965735720688183123354939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29977157147125455415569959 44965735720688183123354939)
            ·
              refine ⟨67448603581032274685032409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44965735720688183123354939 67448603581032274685032409)
              ·
                refine ⟨50586452685774206013774307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67448603581032274685032409 50586452685774206013774307)
                ·
                  refine ⟨75879679028661309020661461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50586452685774206013774307 75879679028661309020661461)
                  ·
                    refine ⟨1778429977234249430171753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 75879679028661309020661461 1778429977234249430171753)
                    ·
                      refine ⟨1333822482925687072628815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778429977234249430171753 1333822482925687072628815)
                      ·
                        rfl

theorem cell23_2597610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_2597610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597610 prefixEnd_2597610 := by exact prefixLift 2597610
  have htrace : WordTrace (prefixWord ++ tailWord_2597610) baseStart_2597610 baseEnd_2597610 := by
    simpa [prefixWord, tailWord_2597610, baseEnd_2597610] using wordTrace_append hprefix tailTrace_2597610
  have hstable : (prefixWord ++ tailWord_2597610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597610).length < 2 ^ (prefixWord ++ tailWord_2597610).sum := by decide
  have hdescent : baseEnd_2597610 < baseStart_2597610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597630 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2597630 : Nat := 118140960795 + 2597630 * 2 ^ 59
def prefixEnd_2597630 : Nat := 4983230072969 + 3 ^ 40 * 2597630 * 2
def baseEnd_2597630 : Nat := 1333832752538776994378723

theorem tailTrace_2597630 : CollatzResearch.WordTrace tailWord_2597630 prefixEnd_2597630 1333832752538776994378723 := by
  unfold tailWord_2597630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842918697404703091141793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63162233052825083152756229 11842918697404703091141793)
  ·
    refine ⟨8882189023053527318356345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11842918697404703091141793 8882189023053527318356345)
    ·
      refine ⟨6661641767290145488767259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8882189023053527318356345 6661641767290145488767259)
      ·
        refine ⟨9992462650935218233150889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6661641767290145488767259 9992462650935218233150889)
        ·
          refine ⟨7494346988201413674863167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9992462650935218233150889 7494346988201413674863167)
          ·
            refine ⟨11241520482302120512294751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494346988201413674863167 11241520482302120512294751)
            ·
              refine ⟨16862280723453180768442127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11241520482302120512294751 16862280723453180768442127)
              ·
                refine ⟨25293421085179771152663191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16862280723453180768442127 25293421085179771152663191)
                ·
                  refine ⟨37940131627769656728994787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25293421085179771152663191 37940131627769656728994787)
                  ·
                    refine ⟨56910197441654485093492181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37940131627769656728994787 56910197441654485093492181)
                    ·
                      refine ⟨1333832752538776994378723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56910197441654485093492181 1333832752538776994378723)
                      ·
                        rfl

theorem cell23_2597630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2597630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597630 prefixEnd_2597630 := by exact prefixLift 2597630
  have htrace : WordTrace (prefixWord ++ tailWord_2597630) baseStart_2597630 baseEnd_2597630 := by
    simpa [prefixWord, tailWord_2597630, baseEnd_2597630] using wordTrace_append hprefix tailTrace_2597630
  have hstable : (prefixWord ++ tailWord_2597630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597630).length < 2 ^ (prefixWord ++ tailWord_2597630).sum := by decide
  have hdescent : baseEnd_2597630 < baseStart_2597630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597667 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 1, 4]
def baseStart_2597667 : Nat := 118140960795 + 2597667 * 2 ^ 59
def prefixEnd_2597667 : Nat := 4983230072969 + 3 ^ 40 * 2597667 * 2
def baseEnd_2597667 : Nat := 444617250440997783205351

theorem tailTrace_2597667 : CollatzResearch.WordTrace tailWord_2597667 prefixEnd_2597667 444617250440997783205351 := by
  unfold tailWord_2597667
  simp only [CollatzResearch.WordTrace]
  refine ⟨94744699080103580048231255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63163132720069053365487503 94744699080103580048231255)
  ·
    refine ⟨142117048620155370072346883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94744699080103580048231255 142117048620155370072346883)
    ·
      refine ⟨213175572930233055108520325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142117048620155370072346883 213175572930233055108520325)
      ·
        refine ⟨39970419924418697832847561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213175572930233055108520325 39970419924418697832847561)
        ·
          refine ⟨29977814943314023374635671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39970419924418697832847561 29977814943314023374635671)
          ·
            refine ⟨44966722414971035061953507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29977814943314023374635671 44966722414971035061953507)
            ·
              refine ⟨67450083622456552592930261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44966722414971035061953507 67450083622456552592930261)
              ·
                refine ⟨1580861334901325451396803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67450083622456552592930261 1580861334901325451396803)
                ·
                  refine ⟨2371292002351988177095205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580861334901325451396803 2371292002351988177095205)
                  ·
                    refine ⟨444617250440997783205351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371292002351988177095205 444617250440997783205351)
                    ·
                      rfl

theorem cell23_2597667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 4].length) (baseStart_2597667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597667 prefixEnd_2597667 := by exact prefixLift 2597667
  have htrace : WordTrace (prefixWord ++ tailWord_2597667) baseStart_2597667 baseEnd_2597667 := by
    simpa [prefixWord, tailWord_2597667, baseEnd_2597667] using wordTrace_append hprefix tailTrace_2597667
  have hstable : (prefixWord ++ tailWord_2597667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597667).length < 2 ^ (prefixWord ++ tailWord_2597667).sum := by decide
  have hdescent : baseEnd_2597667 < baseStart_2597667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597703 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2597703 : Nat := 118140960795 + 2597703 * 2 ^ 59
def prefixEnd_2597703 : Nat := 4983230072969 + 3 ^ 40 * 2597703 * 2
def baseEnd_2597703 : Nat := 1333870236626555208765887

theorem tailTrace_2597703 : CollatzResearch.WordTrace tailWord_2597703 prefixEnd_2597703 1333870236626555208765887 := by
  unfold tailWord_2597703
  simp only [CollatzResearch.WordTrace]
  refine ⟨94746012107973158196541763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63164008071982105464361175 94746012107973158196541763)
  ·
    refine ⟨142119018161959737294812645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94746012107973158196541763 142119018161959737294812645)
    ·
      refine ⟨26647315905367450742777371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142119018161959737294812645 26647315905367450742777371)
      ·
        refine ⟨39970973858051176114166057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26647315905367450742777371 39970973858051176114166057)
        ·
          refine ⟨29978230393538382085624543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39970973858051176114166057 29978230393538382085624543)
          ·
            refine ⟨44967345590307573128436815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29978230393538382085624543 44967345590307573128436815)
            ·
              refine ⟨67451018385461359692655223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44967345590307573128436815 67451018385461359692655223)
              ·
                refine ⟨101176527578192039538982835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67451018385461359692655223 101176527578192039538982835)
                ·
                  refine ⟨151764791367288059308474253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101176527578192039538982835 151764791367288059308474253)
                  ·
                    refine ⟨56911796762733022240677845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151764791367288059308474253 56911796762733022240677845)
                    ·
                      refine ⟨1333870236626555208765887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56911796762733022240677845 1333870236626555208765887)
                      ·
                        rfl

theorem cell23_2597703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2597703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597703 prefixEnd_2597703 := by exact prefixLift 2597703
  have htrace : WordTrace (prefixWord ++ tailWord_2597703) baseStart_2597703 baseEnd_2597703 := by
    simpa [prefixWord, tailWord_2597703, baseEnd_2597703] using wordTrace_append hprefix tailTrace_2597703
  have hstable : (prefixWord ++ tailWord_2597703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597703).length < 2 ^ (prefixWord ++ tailWord_2597703).sum := by decide
  have hdescent : baseEnd_2597703 < baseStart_2597703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597717 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_2597717 : Nat := 118140960795 + 2597717 * 2 ^ 59
def prefixEnd_2597717 : Nat := 4983230072969 + 3 ^ 40 * 2597717 * 2
def baseEnd_2597717 : Nat := 1333877425355718153990823

theorem tailTrace_2597717 : CollatzResearch.WordTrace tailWord_2597717 prefixEnd_2597717 1333877425355718153990823 := by
  unfold tailWord_2597717
  simp only [CollatzResearch.WordTrace]
  refine ⟨94746522729922438587551405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63164348486614959058367603 94746522729922438587551405)
  ·
    refine ⟨35529946023720914470331777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94746522729922438587551405 35529946023720914470331777)
    ·
      refine ⟨26647459517790685852748833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35529946023720914470331777 26647459517790685852748833)
      ·
        refine ⟨19985594638343014389561625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26647459517790685852748833 19985594638343014389561625)
        ·
          refine ⟨14989195978757260792171219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19985594638343014389561625 14989195978757260792171219)
          ·
            refine ⟨22483793968135891188256829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14989195978757260792171219 22483793968135891188256829)
            ·
              refine ⟨8431422738050959195596311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22483793968135891188256829 8431422738050959195596311)
              ·
                refine ⟨12647134107076438793394467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8431422738050959195596311 12647134107076438793394467)
                ·
                  refine ⟨18970701160614658190091701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12647134107076438793394467 18970701160614658190091701)
                  ·
                    refine ⟨1778503233807624205321097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18970701160614658190091701 1778503233807624205321097)
                    ·
                      refine ⟨1333877425355718153990823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778503233807624205321097 1333877425355718153990823)
                      ·
                        rfl

theorem cell23_2597717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_2597717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597717 prefixEnd_2597717 := by exact prefixLift 2597717
  have htrace : WordTrace (prefixWord ++ tailWord_2597717) baseStart_2597717 baseEnd_2597717 := by
    simpa [prefixWord, tailWord_2597717, baseEnd_2597717] using wordTrace_append hprefix tailTrace_2597717
  have hstable : (prefixWord ++ tailWord_2597717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597717).length < 2 ^ (prefixWord ++ tailWord_2597717).sum := by decide
  have hdescent : baseEnd_2597717 < baseStart_2597717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597723 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 9, 6]
def baseStart_2597723 : Nat := 118140960795 + 2597723 * 2 ^ 59
def prefixEnd_2597723 : Nat := 4983230072969 + 3 ^ 40 * 2597723 * 2
def baseEnd_2597723 : Nat := 444626835413215043505265

theorem tailTrace_2597723 : CollatzResearch.WordTrace tailWord_2597723 prefixEnd_2597723 444626835413215043505265 := by
  unfold tailWord_2597723
  simp only [CollatzResearch.WordTrace]
  refine ⟨94746741567900701612269823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63164494378600467741513215 94746741567900701612269823)
  ·
    refine ⟨142120112351851052418404735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94746741567900701612269823 142120112351851052418404735)
    ·
      refine ⟨213180168527776578627607103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142120112351851052418404735 213180168527776578627607103)
      ·
        refine ⟨319770252791664867941410655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213180168527776578627607103 319770252791664867941410655)
        ·
          refine ⟨479655379187497301912115983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319770252791664867941410655 479655379187497301912115983)
          ·
            refine ⟨719483068781245952868173975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479655379187497301912115983 719483068781245952868173975)
            ·
              refine ⟨1079224603171868929302260963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719483068781245952868173975 1079224603171868929302260963)
              ·
                refine ⟨1618836904757803393953391445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079224603171868929302260963 1618836904757803393953391445)
                ·
                  refine ⟨9485372488815254261445653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1618836904757803393953391445 9485372488815254261445653)
                  ·
                    refine ⟨444626835413215043505265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9485372488815254261445653 444626835413215043505265)
                    ·
                      rfl

theorem cell23_2597723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_2597723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597723 prefixEnd_2597723 := by exact prefixLift 2597723
  have htrace : WordTrace (prefixWord ++ tailWord_2597723) baseStart_2597723 baseEnd_2597723 := by
    simpa [prefixWord, tailWord_2597723, baseEnd_2597723] using wordTrace_append hprefix tailTrace_2597723
  have hstable : (prefixWord ++ tailWord_2597723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597723).length < 2 ^ (prefixWord ++ tailWord_2597723).sum := by decide
  have hdescent : baseEnd_2597723 < baseStart_2597723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597757 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_2597757 : Nat := 118140960795 + 2597757 * 2 ^ 59
def prefixEnd_2597757 : Nat := 4983230072969 + 3 ^ 40 * 2597757 * 2
def baseEnd_2597757 : Nat := 444632654860632665830213

theorem tailTrace_2597757 : CollatzResearch.WordTrace tailWord_2597757 prefixEnd_2597757 444632654860632665830213 := by
  unfold tailWord_2597757
  simp only [CollatzResearch.WordTrace]
  refine ⟨94747981649777525419007525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63165321099851683612671683 94747981649777525419007525)
  ·
    refine ⟨17765246559333286016063911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94747981649777525419007525 17765246559333286016063911)
    ·
      refine ⟨26647869838999929024095867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17765246559333286016063911 26647869838999929024095867)
      ·
        refine ⟨39971804758499893536143801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26647869838999929024095867 39971804758499893536143801)
        ·
          refine ⟨29978853568874920152107851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39971804758499893536143801 29978853568874920152107851)
          ·
            refine ⟨44968280353312380228161777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29978853568874920152107851 44968280353312380228161777)
            ·
              refine ⟨33726210264984285171121333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44968280353312380228161777 33726210264984285171121333)
              ·
                refine ⟨3161832212342276734792625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33726210264984285171121333 3161832212342276734792625)
                ·
                  refine ⟨2371374159256707551094469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161832212342276734792625 2371374159256707551094469)
                  ·
                    refine ⟨444632654860632665830213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371374159256707551094469 444632654860632665830213)
                    ·
                      rfl

theorem cell23_2597757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_2597757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597757 prefixEnd_2597757 := by exact prefixLift 2597757
  have htrace : WordTrace (prefixWord ++ tailWord_2597757) baseStart_2597757 baseEnd_2597757 := by
    simpa [prefixWord, tailWord_2597757, baseEnd_2597757] using wordTrace_append hprefix tailTrace_2597757
  have hstable : (prefixWord ++ tailWord_2597757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597757).length < 2 ^ (prefixWord ++ tailWord_2597757).sum := by decide
  have hdescent : baseEnd_2597757 < baseStart_2597757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597760 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_2597760 : Nat := 118140960795 + 2597760 * 2 ^ 59
def prefixEnd_2597760 : Nat := 4983230072969 + 3 ^ 40 * 2597760 * 2
def baseEnd_2597760 : Nat := 1333899505023861485753125

theorem tailTrace_2597760 : CollatzResearch.WordTrace tailWord_2597760 prefixEnd_2597760 1333899505023861485753125 := by
  unfold tailWord_2597760
  simp only [CollatzResearch.WordTrace]
  refine ⟨47374045534383328465683367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63165394045844437954244489 47374045534383328465683367)
  ·
    refine ⟨71061068301574992698525051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47374045534383328465683367 71061068301574992698525051)
    ·
      refine ⟨106591602452362489047787577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71061068301574992698525051 106591602452362489047787577)
      ·
        refine ⟨79943701839271866785840683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106591602452362489047787577 79943701839271866785840683)
        ·
          refine ⟨119915552758907800178761025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79943701839271866785840683 119915552758907800178761025)
          ·
            refine ⟨89936664569180850134070769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119915552758907800178761025 89936664569180850134070769)
            ·
              refine ⟨67452498426885637600553077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89936664569180850134070769 67452498426885637600553077)
              ·
                refine ⟨6323671727520528525051851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67452498426885637600553077 6323671727520528525051851)
                ·
                  refine ⟨9485507591280792787577777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6323671727520528525051851 9485507591280792787577777)
                  ·
                    refine ⟨7114130693460594590683333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9485507591280792787577777 7114130693460594590683333)
                    ·
                      refine ⟨1333899505023861485753125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7114130693460594590683333 1333899505023861485753125)
                      ·
                        rfl

theorem cell23_2597760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_2597760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597760 prefixEnd_2597760 := by exact prefixLift 2597760
  have htrace : WordTrace (prefixWord ++ tailWord_2597760) baseStart_2597760 baseEnd_2597760 := by
    simpa [prefixWord, tailWord_2597760, baseEnd_2597760] using wordTrace_append hprefix tailTrace_2597760
  have hstable : (prefixWord ++ tailWord_2597760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597760).length < 2 ^ (prefixWord ++ tailWord_2597760).sum := by decide
  have hdescent : baseEnd_2597760 < baseStart_2597760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597824 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 3, 3, 2]
def baseStart_2597824 : Nat := 118140960795 + 2597824 * 2 ^ 59
def prefixEnd_2597824 : Nat := 4983230072969 + 3 ^ 40 * 2597824 * 2
def baseEnd_2597824 : Nat := 1333932367785749235352831

theorem tailTrace_2597824 : CollatzResearch.WordTrace tailWord_2597824 prefixEnd_2597824 1333932367785749235352831 := by
  unfold tailWord_2597824
  simp only [CollatzResearch.WordTrace]
  refine ⟨47375212670267397930848263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63166950227023197241131017 47375212670267397930848263)
  ·
    refine ⟨71062819005401096896272395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47375212670267397930848263 71062819005401096896272395)
    ·
      refine ⟨106594228508101645344408593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71062819005401096896272395 106594228508101645344408593)
      ·
        refine ⟨79945671381076234008306445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106594228508101645344408593 79945671381076234008306445)
        ·
          refine ⟨29979626767903587753114917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79945671381076234008306445 29979626767903587753114917)
          ·
            refine ⟨5621180018981922703709047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29979626767903587753114917 5621180018981922703709047)
            ·
              refine ⟨8431770028472884055563571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621180018981922703709047 8431770028472884055563571)
              ·
                refine ⟨12647655042709326083345357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8431770028472884055563571 12647655042709326083345357)
                ·
                  refine ⟨4742870641015997281254509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12647655042709326083345357 4742870641015997281254509)
                  ·
                    refine ⟨1778576490380998980470441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4742870641015997281254509 1778576490380998980470441)
                    ·
                      refine ⟨1333932367785749235352831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778576490380998980470441 1333932367785749235352831)
                      ·
                        rfl

theorem cell23_2597824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_2597824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597824 prefixEnd_2597824 := by exact prefixLift 2597824
  have htrace : WordTrace (prefixWord ++ tailWord_2597824) baseStart_2597824 baseEnd_2597824 := by
    simpa [prefixWord, tailWord_2597824, baseEnd_2597824] using wordTrace_append hprefix tailTrace_2597824
  have hstable : (prefixWord ++ tailWord_2597824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597824).length < 2 ^ (prefixWord ++ tailWord_2597824).sum := by decide
  have hdescent : baseEnd_2597824 < baseStart_2597824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597841 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 1, 3, 2]
def baseStart_2597841 : Nat := 118140960795 + 2597841 * 2 ^ 59
def prefixEnd_2597841 : Nat := 4983230072969 + 3 ^ 40 * 2597841 * 2
def baseEnd_2597841 : Nat := 1333941096956875668840253

theorem tailTrace_2597841 : CollatzResearch.WordTrace tailWord_2597841 prefixEnd_2597841 1333941096956875668840253 := by
  unfold tailWord_2597841
  simp only [CollatzResearch.WordTrace]
  refine ⟨94751045381473207765065377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63167363587648805176710251 94751045381473207765065377)
  ·
    refine ⟨71063284036104905823799033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94751045381473207765065377 71063284036104905823799033)
    ·
      refine ⟨53297463027078679367849275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71063284036104905823799033 53297463027078679367849275)
      ·
        refine ⟨79946194540618019051773913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53297463027078679367849275 79946194540618019051773913)
        ·
          refine ⟨59959645905463514288830435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79946194540618019051773913 59959645905463514288830435)
          ·
            refine ⟨89939468858195271433245653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59959645905463514288830435 89939468858195271433245653)
            ·
              refine ⟨2107956301363951674216695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89939468858195271433245653 2107956301363951674216695)
              ·
                refine ⟨3161934452045927511325043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107956301363951674216695 3161934452045927511325043)
                ·
                  refine ⟨4742901678068891266987565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161934452045927511325043 4742901678068891266987565)
                  ·
                    refine ⟨1778588129275834225120337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4742901678068891266987565 1778588129275834225120337)
                    ·
                      refine ⟨1333941096956875668840253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778588129275834225120337 1333941096956875668840253)
                      ·
                        rfl

theorem cell23_2597841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_2597841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597841 prefixEnd_2597841 := by exact prefixLift 2597841
  have htrace : WordTrace (prefixWord ++ tailWord_2597841) baseStart_2597841 baseEnd_2597841 := by
    simpa [prefixWord, tailWord_2597841, baseEnd_2597841] using wordTrace_append hprefix tailTrace_2597841
  have hstable : (prefixWord ++ tailWord_2597841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597841).length < 2 ^ (prefixWord ++ tailWord_2597841).sum := by decide
  have hdescent : baseEnd_2597841 < baseStart_2597841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597871 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 2, 2, 2]
def baseStart_2597871 : Nat := 118140960795 + 2597871 * 2 ^ 59
def prefixEnd_2597871 : Nat := 4983230072969 + 3 ^ 40 * 2597871 * 2
def baseEnd_2597871 : Nat := 1333956501376510551465115

theorem tailTrace_2597871 : CollatzResearch.WordTrace tailWord_2597871 prefixEnd_2597871 1333956501376510551465115 := by
  unfold tailWord_2597871
  simp only [CollatzResearch.WordTrace]
  refine ⟨94752139571364522888657467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63168093047576348592438311 94752139571364522888657467)
  ·
    refine ⟨142128209357046784332986201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94752139571364522888657467 142128209357046784332986201)
    ·
      refine ⟨106596157017785088249739651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142128209357046784332986201 106596157017785088249739651)
      ·
        refine ⟨159894235526677632374609477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106596157017785088249739651 159894235526677632374609477)
        ·
          refine ⟨29980169161252056070239277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159894235526677632374609477 29980169161252056070239277)
          ·
            refine ⟨11242563435469521026339729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29980169161252056070239277 11242563435469521026339729)
            ·
              refine ⟨8431922576602140769754797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11242563435469521026339729 8431922576602140769754797)
              ·
                refine ⟨3161970966225802788658049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8431922576602140769754797 3161970966225802788658049)
                ·
                  refine ⟨2371478224669352091493537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161970966225802788658049 2371478224669352091493537)
                  ·
                    refine ⟨1778608668502014068620153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2371478224669352091493537 1778608668502014068620153)
                    ·
                      refine ⟨1333956501376510551465115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778608668502014068620153 1333956501376510551465115)
                      ·
                        rfl

theorem cell23_2597871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 2, 2].length) (baseStart_2597871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597871 prefixEnd_2597871 := by exact prefixLift 2597871
  have htrace : WordTrace (prefixWord ++ tailWord_2597871) baseStart_2597871 baseEnd_2597871 := by
    simpa [prefixWord, tailWord_2597871, baseEnd_2597871] using wordTrace_append hprefix tailTrace_2597871
  have hstable : (prefixWord ++ tailWord_2597871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597871).length < 2 ^ (prefixWord ++ tailWord_2597871).sum := by decide
  have hdescent : baseEnd_2597871 < baseStart_2597871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597977 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_2597977 : Nat := 118140960795 + 2597977 * 2 ^ 59
def prefixEnd_2597977 : Nat := 4983230072969 + 3 ^ 40 * 2597977 * 2
def baseEnd_2597977 : Nat := 1334010930325887136739627

theorem tailTrace_2597977 : CollatzResearch.WordTrace tailWord_2597977 prefixEnd_2597977 1334010930325887136739627 := by
  unfold tailWord_2597977
  simp only [CollatzResearch.WordTrace]
  refine ⟨94756005708980502992016185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63170670472653668661344123 94756005708980502992016185)
  ·
    refine ⟨71067004281735377244012139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94756005708980502992016185 71067004281735377244012139)
    ·
      refine ⟨106600506422603065866018209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71067004281735377244012139 106600506422603065866018209)
      ·
        refine ⟨79950379816952299399513657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106600506422603065866018209 79950379816952299399513657)
        ·
          refine ⟨59962784862714224549635243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79950379816952299399513657 59962784862714224549635243)
          ·
            refine ⟨89944177294071336824452865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59962784862714224549635243 89944177294071336824452865)
            ·
              refine ⟨67458132970553502618339649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89944177294071336824452865 67458132970553502618339649)
              ·
                refine ⟨50593599727915126963754737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67458132970553502618339649 50593599727915126963754737)
                ·
                  refine ⟨37945199795936345222816053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50593599727915126963754737 37945199795936345222816053)
                  ·
                    refine ⟨3557362480869032364639005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37945199795936345222816053 3557362480869032364639005)
                    ·
                      refine ⟨1334010930325887136739627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3557362480869032364639005 1334010930325887136739627)
                      ·
                        rfl

theorem cell23_2597977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_2597977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2597977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2597977 prefixEnd_2597977 := by exact prefixLift 2597977
  have htrace : WordTrace (prefixWord ++ tailWord_2597977) baseStart_2597977 baseEnd_2597977 := by
    simpa [prefixWord, tailWord_2597977, baseEnd_2597977] using wordTrace_append hprefix tailTrace_2597977
  have hstable : (prefixWord ++ tailWord_2597977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597977).length < 2 ^ (prefixWord ++ tailWord_2597977).sum := by decide
  have hdescent : baseEnd_2597977 < baseStart_2597977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598044 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2598044 : Nat := 118140960795 + 2598044 * 2 ^ 59
def prefixEnd_2598044 : Nat := 4983230072969 + 3 ^ 40 * 2598044 * 2
def baseEnd_2598044 : Nat := 444681777843246124867273

theorem tailTrace_2598044 : CollatzResearch.WordTrace tailWord_2598044 prefixEnd_2598044 444681777843246124867273 := by
  unfold tailWord_2598044
  simp only [CollatzResearch.WordTrace]
  refine ⟨47379224699868886717352593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63172299599825182289803457 47379224699868886717352593)
  ·
    refine ⟨35534418524901665038014445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47379224699868886717352593 35534418524901665038014445)
    ·
      refine ⟨13325406946838124389255417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35534418524901665038014445 13325406946838124389255417)
      ·
        refine ⟨9994055210128593291941563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13325406946838124389255417 9994055210128593291941563)
        ·
          refine ⟨14991082815192889937912345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9994055210128593291941563 14991082815192889937912345)
          ·
            refine ⟨11243312111394667453434259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14991082815192889937912345 11243312111394667453434259)
            ·
              refine ⟨16864968167092001180151389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11243312111394667453434259 16864968167092001180151389)
              ·
                refine ⟨6324363062659500442556771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16864968167092001180151389 6324363062659500442556771)
                ·
                  refine ⟨9486544593989250663835157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6324363062659500442556771 9486544593989250663835157)
                  ·
                    refine ⟨444681777843246124867273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9486544593989250663835157 444681777843246124867273)
                    ·
                      rfl

theorem cell23_2598044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2598044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598044 prefixEnd_2598044 := by exact prefixLift 2598044
  have htrace : WordTrace (prefixWord ++ tailWord_2598044) baseStart_2598044 baseEnd_2598044 := by
    simpa [prefixWord, tailWord_2598044, baseEnd_2598044] using wordTrace_append hprefix tailTrace_2598044
  have hstable : (prefixWord ++ tailWord_2598044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598044).length < 2 ^ (prefixWord ++ tailWord_2598044).sum := by decide
  have hdescent : baseEnd_2598044 < baseStart_2598044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598055 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2598055 : Nat := 118140960795 + 2598055 * 2 ^ 59
def prefixEnd_2598055 : Nat := 4983230072969 + 3 ^ 40 * 2598055 * 2
def baseEnd_2598055 : Nat := 1334050981816937831564269

theorem tailTrace_2598055 : CollatzResearch.WordTrace tailWord_2598055 prefixEnd_2598055 1334050981816937831564269 := by
  unfold tailWord_2598055
  simp only [CollatzResearch.WordTrace]
  refine ⟨94758850602697922313355619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63172567068465281542237079 94758850602697922313355619)
  ·
    refine ⟨142138275904046883470033429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94758850602697922313355619 142138275904046883470033429)
    ·
      refine ⟨6662731683002197662657817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 142138275904046883470033429 6662731683002197662657817)
      ·
        refine ⟨4997048762251648246993363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6662731683002197662657817 4997048762251648246993363)
        ·
          refine ⟨7495573143377472370490045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997048762251648246993363 7495573143377472370490045)
          ·
            refine ⟨2810839928766552138933767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7495573143377472370490045 2810839928766552138933767)
            ·
              refine ⟨4216259893149828208400651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810839928766552138933767 4216259893149828208400651)
              ·
                refine ⟨6324389839724742312600977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216259893149828208400651 6324389839724742312600977)
                ·
                  refine ⟨4743292379793556734450733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6324389839724742312600977 4743292379793556734450733)
                  ·
                    refine ⟨1778734642422583775419025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4743292379793556734450733 1778734642422583775419025)
                    ·
                      refine ⟨1334050981816937831564269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778734642422583775419025 1334050981816937831564269)
                      ·
                        rfl

theorem cell23_2598055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2598055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598055 prefixEnd_2598055 := by exact prefixLift 2598055
  have htrace : WordTrace (prefixWord ++ tailWord_2598055) baseStart_2598055 baseEnd_2598055 := by
    simpa [prefixWord, tailWord_2598055, baseEnd_2598055] using wordTrace_append hprefix tailTrace_2598055
  have hstable : (prefixWord ++ tailWord_2598055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598055).length < 2 ^ (prefixWord ++ tailWord_2598055).sum := by decide
  have hdescent : baseEnd_2598055 < baseStart_2598055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598071 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_2598071 : Nat := 118140960795 + 2598071 * 2 ^ 59
def prefixEnd_2598071 : Nat := 4983230072969 + 3 ^ 40 * 2598071 * 2
def baseEnd_2598071 : Nat := 1334059197507409768964195

theorem tailTrace_2598071 : CollatzResearch.WordTrace tailWord_2598071 prefixEnd_2598071 1334059197507409768964195 := by
  unfold tailWord_2598071
  simp only [CollatzResearch.WordTrace]
  refine ⟨94759434170639957045938067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63172956113759971363958711 94759434170639957045938067)
  ·
    refine ⟨142139151255959935568907101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94759434170639957045938067 142139151255959935568907101)
    ·
      refine ⟨53302181720984975838340163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142139151255959935568907101 53302181720984975838340163)
      ·
        refine ⟨79953272581477463757510245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53302181720984975838340163 79953272581477463757510245)
        ·
          refine ⟨14991238609027024454533171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79953272581477463757510245 14991238609027024454533171)
          ·
            refine ⟨22486857913540536681799757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14991238609027024454533171 22486857913540536681799757)
            ·
              refine ⟨8432571717577701255674909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22486857913540536681799757 8432571717577701255674909)
              ·
                refine ⟨3162214394091637970878091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8432571717577701255674909 3162214394091637970878091)
                ·
                  refine ⟨4743321591137456956317137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162214394091637970878091 4743321591137456956317137)
                  ·
                    refine ⟨3557491193353092717237853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4743321591137456956317137 3557491193353092717237853)
                    ·
                      refine ⟨1334059197507409768964195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3557491193353092717237853 1334059197507409768964195)
                      ·
                        rfl

theorem cell23_2598071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_2598071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598071 prefixEnd_2598071 := by exact prefixLift 2598071
  have htrace : WordTrace (prefixWord ++ tailWord_2598071) baseStart_2598071 baseEnd_2598071 := by
    simpa [prefixWord, tailWord_2598071, baseEnd_2598071] using wordTrace_append hprefix tailTrace_2598071
  have hstable : (prefixWord ++ tailWord_2598071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598071).length < 2 ^ (prefixWord ++ tailWord_2598071).sum := by decide
  have hdescent : baseEnd_2598071 < baseStart_2598071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598078 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2598078 : Nat := 118140960795 + 2598078 * 2 ^ 59
def prefixEnd_2598078 : Nat := 4983230072969 + 3 ^ 40 * 2598078 * 2
def baseEnd_2598078 : Nat := 444687597290663747192221

theorem tailTrace_2598078 : CollatzResearch.WordTrace tailWord_2598078 prefixEnd_2598078 444687597290663747192221 := by
  unfold tailWord_2598078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844961185201824655180361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63173126321076398160961925 11844961185201824655180361)
  ·
    refine ⟨8883720888901368491385271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11844961185201824655180361 8883720888901368491385271)
    ·
      refine ⟨13325581333352052737077907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8883720888901368491385271 13325581333352052737077907)
      ·
        refine ⟨19988372000028079105616861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325581333352052737077907 19988372000028079105616861)
        ·
          refine ⟨7495639500010529664606323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19988372000028079105616861 7495639500010529664606323)
          ·
            refine ⟨11243459250015794496909485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495639500010529664606323 11243459250015794496909485)
            ·
              refine ⟨4216297218755922936341057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11243459250015794496909485 4216297218755922936341057)
              ·
                refine ⟨3162222914066942202255793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216297218755922936341057 3162222914066942202255793)
                ·
                  refine ⟨2371667185550206651691845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162222914066942202255793 2371667185550206651691845)
                  ·
                    refine ⟨444687597290663747192221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371667185550206651691845 444687597290663747192221)
                    ·
                      rfl

theorem cell23_2598078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2598078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598078 prefixEnd_2598078 := by exact prefixLift 2598078
  have htrace : WordTrace (prefixWord ++ tailWord_2598078) baseStart_2598078 baseEnd_2598078 := by
    simpa [prefixWord, tailWord_2598078, baseEnd_2598078] using wordTrace_append hprefix tailTrace_2598078
  have hstable : (prefixWord ++ tailWord_2598078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598078).length < 2 ^ (prefixWord ++ tailWord_2598078).sum := by decide
  have hdescent : baseEnd_2598078 < baseStart_2598078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598087 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 9]
def baseStart_2598087 : Nat := 118140960795 + 2598087 * 2 ^ 59
def prefixEnd_2598087 : Nat := 4983230072969 + 3 ^ 40 * 2598087 * 2
def baseEnd_2598087 : Nat := 444689137732627235454707

theorem tailTrace_2598087 : CollatzResearch.WordTrace tailWord_2598087 prefixEnd_2598087 444689137732627235454707 := by
  unfold tailWord_2598087
  simp only [CollatzResearch.WordTrace]
  refine ⟨94760017738581991778520515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63173345159054661185680343 94760017738581991778520515)
  ·
    refine ⟨142140026607872987667780773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94760017738581991778520515 142140026607872987667780773)
    ·
      refine ⟨26651254988976185187708895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142140026607872987667780773 26651254988976185187708895)
      ·
        refine ⟨39976882483464277781563343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26651254988976185187708895 39976882483464277781563343)
        ·
          refine ⟨59965323725196416672345015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39976882483464277781563343 59965323725196416672345015)
          ·
            refine ⟨89947985587794625008517523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59965323725196416672345015 89947985587794625008517523)
            ·
              refine ⟨134921978381691937512776285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89947985587794625008517523 134921978381691937512776285)
              ·
                refine ⟨50595741893134476567291107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134921978381691937512776285 50595741893134476567291107)
                ·
                  refine ⟨75893612839701714850936661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50595741893134476567291107 75893612839701714850936661)
                  ·
                    refine ⟨444689137732627235454707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75893612839701714850936661 444689137732627235454707)
                    ·
                      rfl

theorem cell23_2598087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_2598087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598087 prefixEnd_2598087 := by exact prefixLift 2598087
  have htrace : WordTrace (prefixWord ++ tailWord_2598087) baseStart_2598087 baseEnd_2598087 := by
    simpa [prefixWord, tailWord_2598087, baseEnd_2598087] using wordTrace_append hprefix tailTrace_2598087
  have hstable : (prefixWord ++ tailWord_2598087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598087).length < 2 ^ (prefixWord ++ tailWord_2598087).sum := by decide
  have hdescent : baseEnd_2598087 < baseStart_2598087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598111 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 3, 3, 2]
def baseStart_2598111 : Nat := 118140960795 + 2598111 * 2 ^ 59
def prefixEnd_2598111 : Nat := 4983230072969 + 3 ^ 40 * 2598111 * 2
def baseEnd_2598111 : Nat := 1334079736733589612464011

theorem tailTrace_2598111 : CollatzResearch.WordTrace tailWord_2598111 prefixEnd_2598111 1334079736733589612464011 := by
  unfold tailWord_2598111
  simp only [CollatzResearch.WordTrace]
  refine ⟨94760893090495043877394187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63173928726996695918262791 94760893090495043877394187)
  ·
    refine ⟨142141339635742565816091281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94760893090495043877394187 142141339635742565816091281)
    ·
      refine ⟨106606004726806924362068461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142141339635742565816091281 106606004726806924362068461)
      ·
        refine ⟨39977251772552596635775673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106606004726806924362068461 39977251772552596635775673)
        ·
          refine ⟨29982938829414447476831755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39977251772552596635775673 29982938829414447476831755)
          ·
            refine ⟨44974408244121671215247633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29982938829414447476831755 44974408244121671215247633)
            ·
              refine ⟨33730806183091253411435725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44974408244121671215247633 33730806183091253411435725)
              ·
                refine ⟨12649052318659220029288397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33730806183091253411435725 12649052318659220029288397)
                ·
                  refine ⟨4743394619497207510983149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12649052318659220029288397 4743394619497207510983149)
                  ·
                    refine ⟨1778772982311452816618681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4743394619497207510983149 1778772982311452816618681)
                    ·
                      refine ⟨1334079736733589612464011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778772982311452816618681 1334079736733589612464011)
                      ·
                        rfl

theorem cell23_2598111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_2598111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598111 prefixEnd_2598111 := by exact prefixLift 2598111
  have htrace : WordTrace (prefixWord ++ tailWord_2598111) baseStart_2598111 baseEnd_2598111 := by
    simpa [prefixWord, tailWord_2598111, baseEnd_2598111] using wordTrace_append hprefix tailTrace_2598111
  have hstable : (prefixWord ++ tailWord_2598111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598111).length < 2 ^ (prefixWord ++ tailWord_2598111).sum := by decide
  have hdescent : baseEnd_2598111 < baseStart_2598111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598119 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2598119 : Nat := 118140960795 + 2598119 * 2 ^ 59
def prefixEnd_2598119 : Nat := 4983230072969 + 3 ^ 40 * 2598119 * 2
def baseEnd_2598119 : Nat := 1334083844578825581163975

theorem tailTrace_2598119 : CollatzResearch.WordTrace tailWord_2598119 prefixEnd_2598119 1334083844578825581163975 := by
  unfold tailWord_2598119
  simp only [CollatzResearch.WordTrace]
  refine ⟨94761184874466061243685411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63174123249644040829123607 94761184874466061243685411)
  ·
    refine ⟨142141777311699091865528117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94761184874466061243685411 142141777311699091865528117)
    ·
      refine ⟨13325791622971789862393261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142141777311699091865528117 13325791622971789862393261)
      ·
        refine ⟨4997171858614421198397473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13325791622971789862393261 4997171858614421198397473)
        ·
          refine ⟨3747878893960815898798105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997171858614421198397473 3747878893960815898798105)
          ·
            refine ⟨2810909170470611924098579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747878893960815898798105 2810909170470611924098579)
            ·
              refine ⟨4216363755705917886147869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810909170470611924098579 4216363755705917886147869)
              ·
                refine ⟨1581136408389719207305451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4216363755705917886147869 1581136408389719207305451)
                ·
                  refine ⟨2371704612584578810958177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581136408389719207305451 2371704612584578810958177)
                  ·
                    refine ⟨1778778459438434108218633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2371704612584578810958177 1778778459438434108218633)
                    ·
                      refine ⟨1334083844578825581163975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778778459438434108218633 1334083844578825581163975)
                      ·
                        rfl

theorem cell23_2598119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2598119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598119 prefixEnd_2598119 := by exact prefixLift 2598119
  have htrace : WordTrace (prefixWord ++ tailWord_2598119) baseStart_2598119 baseEnd_2598119 := by
    simpa [prefixWord, tailWord_2598119, baseEnd_2598119] using wordTrace_append hprefix tailTrace_2598119
  have hstable : (prefixWord ++ tailWord_2598119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598119).length < 2 ^ (prefixWord ++ tailWord_2598119).sum := by decide
  have hdescent : baseEnd_2598119 < baseStart_2598119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598144 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_2598144 : Nat := 118140960795 + 2598144 * 2 ^ 59
def prefixEnd_2598144 : Nat := 4983230072969 + 3 ^ 40 * 2598144 * 2
def baseEnd_2598144 : Nat := 1334096681595187983351359

theorem tailTrace_2598144 : CollatzResearch.WordTrace tailWord_2598144 prefixEnd_2598144 1334096681595187983351359 := by
  unfold tailWord_2598144
  simp only [CollatzResearch.WordTrace]
  refine ⟨47381048349687745256672743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63174731132916993675563657 47381048349687745256672743)
  ·
    refine ⟨71071572524531617885009115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47381048349687745256672743 71071572524531617885009115)
    ·
      refine ⟨106607358786797426827513673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71071572524531617885009115 106607358786797426827513673)
      ·
        refine ⟨79955519090098070120635255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106607358786797426827513673 79955519090098070120635255)
        ·
          refine ⟨119933278635147105180952883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79955519090098070120635255 119933278635147105180952883)
          ·
            refine ⟨179899917952720657771429325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119933278635147105180952883 179899917952720657771429325)
            ·
              refine ⟨67462469232270246664285997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179899917952720657771429325 67462469232270246664285997)
              ·
                refine ⟨25298425962101342499107249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67462469232270246664285997 25298425962101342499107249)
                ·
                  refine ⟨18973819471576006874330437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25298425962101342499107249 18973819471576006874330437)
                  ·
                    refine ⟨3557591150920501288936957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18973819471576006874330437 3557591150920501288936957)
                    ·
                      refine ⟨1334096681595187983351359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3557591150920501288936957 1334096681595187983351359)
                      ·
                        rfl

theorem cell23_2598144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_2598144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598144 prefixEnd_2598144 := by exact prefixLift 2598144
  have htrace : WordTrace (prefixWord ++ tailWord_2598144) baseStart_2598144 baseEnd_2598144 := by
    simpa [prefixWord, tailWord_2598144, baseEnd_2598144] using wordTrace_append hprefix tailTrace_2598144
  have hstable : (prefixWord ++ tailWord_2598144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598144).length < 2 ^ (prefixWord ++ tailWord_2598144).sum := by decide
  have hdescent : baseEnd_2598144 < baseStart_2598144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598152 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_2598152 : Nat := 118140960795 + 2598152 * 2 ^ 59
def prefixEnd_2598152 : Nat := 4983230072969 + 3 ^ 40 * 2598152 * 2
def baseEnd_2598152 : Nat := 1334100789440423952051323

theorem tailTrace_2598152 : CollatzResearch.WordTrace tailWord_2598152 prefixEnd_2598152 1334100789440423952051323 := by
  unfold tailWord_2598152
  simp only [CollatzResearch.WordTrace]
  refine ⟨47381194241673253939818355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63174925655564338586424473 47381194241673253939818355)
  ·
    refine ⟨71071791362509880909727533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47381194241673253939818355 71071791362509880909727533)
    ·
      refine ⟨26651921760941205341147825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71071791362509880909727533 26651921760941205341147825)
      ·
        refine ⟨19988941320705904005860869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26651921760941205341147825 19988941320705904005860869)
        ·
          refine ⟨3747926497632357001098913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19988941320705904005860869 3747926497632357001098913)
          ·
            refine ⟨2810944873224267750824185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747926497632357001098913 2810944873224267750824185)
            ·
              refine ⟨2108208654918200813118139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810944873224267750824185 2108208654918200813118139)
              ·
                refine ⟨3162312982377301219677209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108208654918200813118139 3162312982377301219677209)
                ·
                  refine ⟨2371734736782975914757907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162312982377301219677209 2371734736782975914757907)
                  ·
                    refine ⟨3557602105174463872136861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2371734736782975914757907 3557602105174463872136861)
                    ·
                      refine ⟨1334100789440423952051323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3557602105174463872136861 1334100789440423952051323)
                      ·
                        rfl

theorem cell23_2598152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_2598152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598152 prefixEnd_2598152 := by exact prefixLift 2598152
  have htrace : WordTrace (prefixWord ++ tailWord_2598152) baseStart_2598152 baseEnd_2598152 := by
    simpa [prefixWord, tailWord_2598152, baseEnd_2598152] using wordTrace_append hprefix tailTrace_2598152
  have hstable : (prefixWord ++ tailWord_2598152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598152).length < 2 ^ (prefixWord ++ tailWord_2598152).sum := by decide
  have hdescent : baseEnd_2598152 < baseStart_2598152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598154 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_2598154 : Nat := 118140960795 + 2598154 * 2 ^ 59
def prefixEnd_2598154 : Nat := 4983230072969 + 3 ^ 40 * 2598154 * 2
def baseEnd_2598154 : Nat := 1334101816401732944226313

theorem tailTrace_2598154 : CollatzResearch.WordTrace tailWord_2598154 prefixEnd_2598154 1334101816401732944226313 := by
  unfold tailWord_2598154
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690615357334815555302379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63174974286226174814139677 23690615357334815555302379)
  ·
    refine ⟨35535923036002223332953569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23690615357334815555302379 35535923036002223332953569)
    ·
      refine ⟨26651942277001667499715177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35535923036002223332953569 26651942277001667499715177)
      ·
        refine ⟨19988956707751250624786383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26651942277001667499715177 19988956707751250624786383)
        ·
          refine ⟨29983435061626875937179575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19988956707751250624786383 29983435061626875937179575)
          ·
            refine ⟨44975152592440313905769363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29983435061626875937179575 44975152592440313905769363)
            ·
              refine ⟨67462728888660470858654045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44975152592440313905769363 67462728888660470858654045)
              ·
                refine ⟨25298523333247676571995267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67462728888660470858654045 25298523333247676571995267)
                ·
                  refine ⟨37947784999871514857992901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25298523333247676571995267 37947784999871514857992901)
                  ·
                    refine ⟨7115209687475909035873669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37947784999871514857992901 7115209687475909035873669)
                    ·
                      refine ⟨1334101816401732944226313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7115209687475909035873669 1334101816401732944226313)
                      ·
                        rfl

theorem cell23_2598154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_2598154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598154 prefixEnd_2598154 := by exact prefixLift 2598154
  have htrace : WordTrace (prefixWord ++ tailWord_2598154) baseStart_2598154 baseEnd_2598154 := by
    simpa [prefixWord, tailWord_2598154, baseEnd_2598154] using wordTrace_append hprefix tailTrace_2598154
  have hstable : (prefixWord ++ tailWord_2598154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598154).length < 2 ^ (prefixWord ++ tailWord_2598154).sum := by decide
  have hdescent : baseEnd_2598154 < baseStart_2598154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598162 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2598162 : Nat := 118140960795 + 2598162 * 2 ^ 59
def prefixEnd_2598162 : Nat := 4983230072969 + 3 ^ 40 * 2598162 * 2
def baseEnd_2598162 : Nat := 1334105924246968912926277

theorem tailTrace_2598162 : CollatzResearch.WordTrace tailWord_2598162 prefixEnd_2598162 1334105924246968912926277 := by
  unfold tailWord_2598162
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690688303327569896875185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63175168808873519725000493 23690688303327569896875185)
  ·
    refine ⟨17768016227495677422656389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23690688303327569896875185 17768016227495677422656389)
    ·
      refine ⟨3331503042655439516748073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17768016227495677422656389 3331503042655439516748073)
      ·
        refine ⟨2498627281991579637561055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3331503042655439516748073 2498627281991579637561055)
        ·
          refine ⟨3747940922987369456341583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498627281991579637561055 3747940922987369456341583)
          ·
            refine ⟨5621911384481054184512375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747940922987369456341583 5621911384481054184512375)
            ·
              refine ⟨8432867076721581276768563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621911384481054184512375 8432867076721581276768563)
              ·
                refine ⟨12649300615082371915152845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8432867076721581276768563 12649300615082371915152845)
                ·
                  refine ⟨4743487730655889468182317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12649300615082371915152845 4743487730655889468182317)
                  ·
                    refine ⟨1778807898995958550568369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4743487730655889468182317 1778807898995958550568369)
                    ·
                      refine ⟨1334105924246968912926277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778807898995958550568369 1334105924246968912926277)
                      ·
                        rfl

theorem cell23_2598162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2598162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598162 prefixEnd_2598162 := by exact prefixLift 2598162
  have htrace : WordTrace (prefixWord ++ tailWord_2598162) baseStart_2598162 baseEnd_2598162 := by
    simpa [prefixWord, tailWord_2598162, baseEnd_2598162] using wordTrace_append hprefix tailTrace_2598162
  have hstable : (prefixWord ++ tailWord_2598162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598162).length < 2 ^ (prefixWord ++ tailWord_2598162).sum := by decide
  have hdescent : baseEnd_2598162 < baseStart_2598162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598230 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2598230 : Nat := 118140960795 + 2598230 * 2 ^ 59
def prefixEnd_2598230 : Nat := 4983230072969 + 3 ^ 40 * 2598230 * 2
def baseEnd_2598230 : Nat := 1334140840931474646875965

theorem tailTrace_2598230 : CollatzResearch.WordTrace tailWord_2598230 prefixEnd_2598230 1334140840931474646875965 := by
  unfold tailWord_2598230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5922827086066495450061009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63176822251375951467317429 5922827086066495450061009)
  ·
    refine ⟨4442120314549871587545757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5922827086066495450061009 4442120314549871587545757)
    ·
      refine ⟨1665795117956201845329659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4442120314549871587545757 1665795117956201845329659)
      ·
        refine ⟨2498692676934302767994489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665795117956201845329659 2498692676934302767994489)
        ·
          refine ⟨1874019507700727075995867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2498692676934302767994489 1874019507700727075995867)
          ·
            refine ⟨2811029261551090613993801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874019507700727075995867 2811029261551090613993801)
            ·
              refine ⟨2108271946163317960495351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811029261551090613993801 2108271946163317960495351)
              ·
                refine ⟨3162407919244976940743027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108271946163317960495351 3162407919244976940743027)
                ·
                  refine ⟨4743611878867465411114541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162407919244976940743027 4743611878867465411114541)
                  ·
                    refine ⟨1778854454575299529167953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4743611878867465411114541 1778854454575299529167953)
                    ·
                      refine ⟨1334140840931474646875965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778854454575299529167953 1334140840931474646875965)
                      ·
                        rfl

theorem cell23_2598230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2598230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598230 prefixEnd_2598230 := by exact prefixLift 2598230
  have htrace : WordTrace (prefixWord ++ tailWord_2598230) baseStart_2598230 baseEnd_2598230 := by
    simpa [prefixWord, tailWord_2598230, baseEnd_2598230] using wordTrace_append hprefix tailTrace_2598230
  have hstable : (prefixWord ++ tailWord_2598230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598230).length < 2 ^ (prefixWord ++ tailWord_2598230).sum := by decide
  have hdescent : baseEnd_2598230 < baseStart_2598230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598231 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_2598231 : Nat := 118140960795 + 2598231 * 2 ^ 59
def prefixEnd_2598231 : Nat := 4983230072969 + 3 ^ 40 * 2598231 * 2
def baseEnd_2598231 : Nat := 1334141354412129142963459

theorem tailTrace_2598231 : CollatzResearch.WordTrace tailWord_2598231 prefixEnd_2598231 1334141354412129142963459 := by
  unfold tailWord_2598231
  simp only [CollatzResearch.WordTrace]
  refine ⟨94765269850060304371762547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63176846566706869581175031 94765269850060304371762547)
  ·
    refine ⟨142147904775090456557643821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94765269850060304371762547 142147904775090456557643821)
    ·
      refine ⟨53305464290658921209116433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142147904775090456557643821 53305464290658921209116433)
      ·
        refine ⟨39979098217994190906837325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53305464290658921209116433 39979098217994190906837325)
        ·
          refine ⟨14992161831747821590063997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39979098217994190906837325 14992161831747821590063997)
          ·
            refine ⟨5622060686905433096273999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14992161831747821590063997 5622060686905433096273999)
            ·
              refine ⟨8433091030358149644410999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622060686905433096273999 8433091030358149644410999)
              ·
                refine ⟨12649636545537224466616499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8433091030358149644410999 12649636545537224466616499)
                ·
                  refine ⟨18974454818305836699924749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12649636545537224466616499 18974454818305836699924749)
                  ·
                    refine ⟨7115420556864688762471781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18974454818305836699924749 7115420556864688762471781)
                    ·
                      refine ⟨1334141354412129142963459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7115420556864688762471781 1334141354412129142963459)
                      ·
                        rfl

theorem cell23_2598231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_2598231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598231 prefixEnd_2598231 := by exact prefixLift 2598231
  have htrace : WordTrace (prefixWord ++ tailWord_2598231) baseStart_2598231 baseEnd_2598231 := by
    simpa [prefixWord, tailWord_2598231, baseEnd_2598231] using wordTrace_append hprefix tailTrace_2598231
  have hstable : (prefixWord ++ tailWord_2598231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598231).length < 2 ^ (prefixWord ++ tailWord_2598231).sum := by decide
  have hdescent : baseEnd_2598231 < baseStart_2598231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598258 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_2598258 : Nat := 118140960795 + 2598258 * 2 ^ 59
def prefixEnd_2598258 : Nat := 4983230072969 + 3 ^ 40 * 2598258 * 2
def baseEnd_2598258 : Nat := 444718406129933512441945

theorem tailTrace_2598258 : CollatzResearch.WordTrace tailWord_2598258 prefixEnd_2598258 444718406129933512441945 := by
  unfold tailWord_2598258
  simp only [CollatzResearch.WordTrace]
  refine ⟨23691563655240621995748857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63177503080641658655330285 23691563655240621995748857)
  ·
    refine ⟨17768672741430466496811643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23691563655240621995748857 17768672741430466496811643)
    ·
      refine ⟨26653009112145699745217465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17768672741430466496811643 26653009112145699745217465)
      ·
        refine ⟨19989756834109274808913099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26653009112145699745217465 19989756834109274808913099)
        ·
          refine ⟨29984635251163912213369649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19989756834109274808913099 29984635251163912213369649)
          ·
            refine ⟨22488476438372934160027237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29984635251163912213369649 22488476438372934160027237)
            ·
              refine ⟨4216589332194925155005107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22488476438372934160027237 4216589332194925155005107)
              ·
                refine ⟨6324883998292387732507661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216589332194925155005107 6324883998292387732507661)
                ·
                  refine ⟨2371831499359645399690373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6324883998292387732507661 2371831499359645399690373)
                  ·
                    refine ⟨444718406129933512441945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371831499359645399690373 444718406129933512441945)
                    ·
                      rfl

theorem cell23_2598258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_2598258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598258 prefixEnd_2598258 := by exact prefixLift 2598258
  have htrace : WordTrace (prefixWord ++ tailWord_2598258) baseStart_2598258 baseEnd_2598258 := by
    simpa [prefixWord, tailWord_2598258, baseEnd_2598258] using wordTrace_append hprefix tailTrace_2598258
  have hstable : (prefixWord ++ tailWord_2598258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598258).length < 2 ^ (prefixWord ++ tailWord_2598258).sum := by decide
  have hdescent : baseEnd_2598258 < baseStart_2598258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598292 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2598292 : Nat := 118140960795 + 2598292 * 2 ^ 59
def prefixEnd_2598292 : Nat := 4983230072969 + 3 ^ 40 * 2598292 * 2
def baseEnd_2598292 : Nat := 444724225577351134766893

theorem tailTrace_2598292 : CollatzResearch.WordTrace tailWord_2598292 prefixEnd_2598292 444724225577351134766893 := by
  unfold tailWord_2598292
  simp only [CollatzResearch.WordTrace]
  refine ⟨47383747351419655894866565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63178329801892874526488753 47383747351419655894866565)
  ·
    refine ⟨8884452628391185480287481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47383747351419655894866565 8884452628391185480287481)
    ·
      refine ⟨6663339471293389110215611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8884452628391185480287481 6663339471293389110215611)
      ·
        refine ⟨9995009206940083665323417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6663339471293389110215611 9995009206940083665323417)
        ·
          refine ⟨7496256905205062748992563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9995009206940083665323417 7496256905205062748992563)
          ·
            refine ⟨11244385357807594123488845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496256905205062748992563 11244385357807594123488845)
            ·
              refine ⟨4216644509177847796308317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11244385357807594123488845 4216644509177847796308317)
              ·
                refine ⟨1581241690941692923615619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4216644509177847796308317 1581241690941692923615619)
                ·
                  refine ⟨2371862536412539385423429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581241690941692923615619 2371862536412539385423429)
                  ·
                    refine ⟨444724225577351134766893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371862536412539385423429 444724225577351134766893)
                    ·
                      rfl

theorem cell23_2598292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2598292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598292 prefixEnd_2598292 := by exact prefixLift 2598292
  have htrace : WordTrace (prefixWord ++ tailWord_2598292) baseStart_2598292 baseEnd_2598292 := by
    simpa [prefixWord, tailWord_2598292, baseEnd_2598292] using wordTrace_append hprefix tailTrace_2598292
  have hstable : (prefixWord ++ tailWord_2598292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598292).length < 2 ^ (prefixWord ++ tailWord_2598292).sum := by decide
  have hdescent : baseEnd_2598292 < baseStart_2598292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598302 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2598302 : Nat := 118140960795 + 2598302 * 2 ^ 59
def prefixEnd_2598302 : Nat := 4983230072969 + 3 ^ 40 * 2598302 * 2
def baseEnd_2598302 : Nat := 1334177811538598365175633

theorem tailTrace_2598302 : CollatzResearch.WordTrace tailWord_2598302 prefixEnd_2598302 1334177811538598365175633 := by
  unfold tailWord_2598302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845982429100385437199645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63178572955202055665064773 11845982429100385437199645)
  ·
    refine ⟨4442243410912644538949867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11845982429100385437199645 4442243410912644538949867)
    ·
      refine ⟨6663365116368966808424801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4442243410912644538949867 6663365116368966808424801)
      ·
        refine ⟨4997523837276725106318601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6663365116368966808424801 4997523837276725106318601)
        ·
          refine ⟨3748142877957543829738951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997523837276725106318601 3748142877957543829738951)
          ·
            refine ⟨5622214316936315744608427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748142877957543829738951 5622214316936315744608427)
            ·
              refine ⟨8433321475404473616912641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622214316936315744608427 8433321475404473616912641)
              ·
                refine ⟨6324991106553355212684481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433321475404473616912641 6324991106553355212684481)
                ·
                  refine ⟨4743743329915016409513361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6324991106553355212684481 4743743329915016409513361)
                  ·
                    refine ⟨3557807497436262307135021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4743743329915016409513361 3557807497436262307135021)
                    ·
                      refine ⟨1334177811538598365175633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3557807497436262307135021 1334177811538598365175633)
                      ·
                        rfl

theorem cell23_2598302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2598302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598302 prefixEnd_2598302 := by exact prefixLift 2598302
  have htrace : WordTrace (prefixWord ++ tailWord_2598302) baseStart_2598302 baseEnd_2598302 := by
    simpa [prefixWord, tailWord_2598302, baseEnd_2598302] using wordTrace_append hprefix tailTrace_2598302
  have hstable : (prefixWord ++ tailWord_2598302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598302).length < 2 ^ (prefixWord ++ tailWord_2598302).sum := by decide
  have hdescent : baseEnd_2598302 < baseStart_2598302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598348 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_2598348 : Nat := 118140960795 + 2598348 * 2 ^ 59
def prefixEnd_2598348 : Nat := 4983230072969 + 3 ^ 40 * 2598348 * 2
def baseEnd_2598348 : Nat := 444733810549568395066807

theorem tailTrace_2598348 : CollatzResearch.WordTrace tailWord_2598348 prefixEnd_2598348 444733810549568395066807 := by
  unfold tailWord_2598348
  simp only [CollatzResearch.WordTrace]
  refine ⟨47384768595318216676885849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63179691460424288902514465 47384768595318216676885849)
  ·
    refine ⟨35538576446488662507664387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47384768595318216676885849 35538576446488662507664387)
    ·
      refine ⟨53307864669732993761496581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35538576446488662507664387 53307864669732993761496581)
      ·
        refine ⟨9995224625574936330280609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53307864669732993761496581 9995224625574936330280609)
        ·
          refine ⟨7496418469181202247710457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9995224625574936330280609 7496418469181202247710457)
          ·
            refine ⟨5622313851885901685782843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7496418469181202247710457 5622313851885901685782843)
            ·
              refine ⟨8433470777828852528674265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622313851885901685782843 8433470777828852528674265)
              ·
                refine ⟨6325103083371639396505699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433470777828852528674265 6325103083371639396505699)
                ·
                  refine ⟨9487654625057459094758549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325103083371639396505699 9487654625057459094758549)
                  ·
                    refine ⟨444733810549568395066807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9487654625057459094758549 444733810549568395066807)
                    ·
                      rfl

theorem cell23_2598348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_2598348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598348 prefixEnd_2598348 := by exact prefixLift 2598348
  have htrace : WordTrace (prefixWord ++ tailWord_2598348) baseStart_2598348 baseEnd_2598348 := by
    simpa [prefixWord, tailWord_2598348, baseEnd_2598348] using wordTrace_append hprefix tailTrace_2598348
  have hstable : (prefixWord ++ tailWord_2598348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598348).length < 2 ^ (prefixWord ++ tailWord_2598348).sum := by decide
  have hdescent : baseEnd_2598348 < baseStart_2598348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598351 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_2598351 : Nat := 118140960795 + 2598351 * 2 ^ 59
def prefixEnd_2598351 : Nat := 4983230072969 + 3 ^ 40 * 2598351 * 2
def baseEnd_2598351 : Nat := 1334202972090668673462907

theorem tailTrace_2598351 : CollatzResearch.WordTrace tailWord_2598351 prefixEnd_2598351 1334202972090668673462907 := by
  unfold tailWord_2598351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94769646609625564866130907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63179764406417043244087271 94769646609625564866130907)
  ·
    refine ⟨142154469914438347299196361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94769646609625564866130907 142154469914438347299196361)
    ·
      refine ⟨106615852435828760474397271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142154469914438347299196361 106615852435828760474397271)
      ·
        refine ⟨159923778653743140711595907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106615852435828760474397271 159923778653743140711595907)
        ·
          refine ⟨239885667980614711067393861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159923778653743140711595907 239885667980614711067393861)
          ·
            refine ⟨44978562746365258325136349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239885667980614711067393861 44978562746365258325136349)
            ·
              refine ⟨16866961029886971871926131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44978562746365258325136349 16866961029886971871926131)
              ·
                refine ⟨25300441544830457807889197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16866961029886971871926131 25300441544830457807889197)
                ·
                  refine ⟨9487665579311421677958449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25300441544830457807889197 9487665579311421677958449)
                  ·
                    refine ⟨7115749184483566258468837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9487665579311421677958449 7115749184483566258468837)
                    ·
                      refine ⟨1334202972090668673462907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7115749184483566258468837 1334202972090668673462907)
                      ·
                        rfl

theorem cell23_2598351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_2598351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598351 prefixEnd_2598351 := by exact prefixLift 2598351
  have htrace : WordTrace (prefixWord ++ tailWord_2598351) baseStart_2598351 baseEnd_2598351 := by
    simpa [prefixWord, tailWord_2598351, baseEnd_2598351] using wordTrace_append hprefix tailTrace_2598351
  have hstable : (prefixWord ++ tailWord_2598351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598351).length < 2 ^ (prefixWord ++ tailWord_2598351).sum := by decide
  have hdescent : baseEnd_2598351 < baseStart_2598351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598365 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2598365 : Nat := 118140960795 + 2598365 * 2 ^ 59
def prefixEnd_2598365 : Nat := 4983230072969 + 3 ^ 40 * 2598365 * 2
def baseEnd_2598365 : Nat := 444736720273277206229281

theorem tailTrace_2598365 : CollatzResearch.WordTrace tailWord_2598365 prefixEnd_2598365 444736720273277206229281 := by
  unfold tailWord_2598365
  simp only [CollatzResearch.WordTrace]
  refine ⟨94770157231574845257140549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63180104821049896838093699 94770157231574845257140549)
  ·
    refine ⟨17769404480920283485713853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94770157231574845257140549 17769404480920283485713853)
    ·
      refine ⟨6663526680345106307142695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17769404480920283485713853 6663526680345106307142695)
      ·
        refine ⟨9995290020517659460714043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6663526680345106307142695 9995290020517659460714043)
        ·
          refine ⟨14992935030776489191071065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9995290020517659460714043 14992935030776489191071065)
          ·
            refine ⟨11244701273082366893303299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14992935030776489191071065 11244701273082366893303299)
            ·
              refine ⟨16867051909623550339954949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11244701273082366893303299 16867051909623550339954949)
              ·
                refine ⟨3162572233054415688741553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16867051909623550339954949 3162572233054415688741553)
                ·
                  refine ⟨2371929174790811766556165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162572233054415688741553 2371929174790811766556165)
                  ·
                    refine ⟨444736720273277206229281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371929174790811766556165 444736720273277206229281)
                    ·
                      rfl

theorem cell23_2598365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2598365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598365 prefixEnd_2598365 := by exact prefixLift 2598365
  have htrace : WordTrace (prefixWord ++ tailWord_2598365) baseStart_2598365 baseEnd_2598365 := by
    simpa [prefixWord, tailWord_2598365, baseEnd_2598365] using wordTrace_append hprefix tailTrace_2598365
  have hstable : (prefixWord ++ tailWord_2598365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598365).length < 2 ^ (prefixWord ++ tailWord_2598365).sum := by decide
  have hdescent : baseEnd_2598365 < baseStart_2598365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598389 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2598389 : Nat := 118140960795 + 2598389 * 2 ^ 59
def prefixEnd_2598389 : Nat := 4983230072969 + 3 ^ 40 * 2598389 * 2
def baseEnd_2598389 : Nat := 1334222484355539524787733

theorem tailTrace_2598389 : CollatzResearch.WordTrace tailWord_2598389 prefixEnd_2598389 1334222484355539524787733 := by
  unfold tailWord_2598389
  simp only [CollatzResearch.WordTrace]
  refine ⟨94771032583487897356014221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63180688388991931570676147 94771032583487897356014221)
  ·
    refine ⟨35539137218807961508505333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94771032583487897356014221 35539137218807961508505333)
    ·
      refine ⟨3331794114263246391422375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35539137218807961508505333 3331794114263246391422375)
      ·
        refine ⟨4997691171394869587133563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3331794114263246391422375 4997691171394869587133563)
        ·
          refine ⟨7496536757092304380700345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997691171394869587133563 7496536757092304380700345)
          ·
            refine ⟨5622402567819228285525259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7496536757092304380700345 5622402567819228285525259)
            ·
              refine ⟨8433603851728842428287889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622402567819228285525259 8433603851728842428287889)
              ·
                refine ⟨6325202888796631821215917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433603851728842428287889 6325202888796631821215917)
                ·
                  refine ⟨2371951083298736932955969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6325202888796631821215917 2371951083298736932955969)
                  ·
                    refine ⟨1778963312474052699716977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2371951083298736932955969 1778963312474052699716977)
                    ·
                      refine ⟨1334222484355539524787733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1778963312474052699716977 1334222484355539524787733)
                      ·
                        rfl

theorem cell23_2598389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2598389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598389 prefixEnd_2598389 := by exact prefixLift 2598389
  have htrace : WordTrace (prefixWord ++ tailWord_2598389) baseStart_2598389 baseEnd_2598389 := by
    simpa [prefixWord, tailWord_2598389, baseEnd_2598389] using wordTrace_append hprefix tailTrace_2598389
  have hstable : (prefixWord ++ tailWord_2598389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598389).length < 2 ^ (prefixWord ++ tailWord_2598389).sum := by decide
  have hdescent : baseEnd_2598389 < baseStart_2598389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598406 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2598406 : Nat := 118140960795 + 2598406 * 2 ^ 59
def prefixEnd_2598406 : Nat := 4983230072969 + 3 ^ 40 * 2598406 * 2
def baseEnd_2598406 : Nat := 1334231213526665958275155

theorem tailTrace_2598406 : CollatzResearch.WordTrace tailWord_2598406 prefixEnd_2598406 1334231213526665958275155 := by
  unfold tailWord_2598406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961614144513322164355721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63181101749617539506255381 2961614144513322164355721)
  ·
    refine ⟨2221210608384991623266791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2961614144513322164355721 2221210608384991623266791)
    ·
      refine ⟨3331815912577487434900187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2221210608384991623266791 3331815912577487434900187)
      ·
        refine ⟨4997723868866231152350281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3331815912577487434900187 4997723868866231152350281)
        ·
          refine ⟨3748292901649673364262711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997723868866231152350281 3748292901649673364262711)
          ·
            refine ⟨5622439352474510046394067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748292901649673364262711 5622439352474510046394067)
            ·
              refine ⟨8433659028711765069591101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622439352474510046394067 8433659028711765069591101)
              ·
                refine ⟨3162622135766911901096663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8433659028711765069591101 3162622135766911901096663)
                ·
                  refine ⟨4743933203650367851644995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162622135766911901096663 4743933203650367851644995)
                  ·
                    refine ⟨7115899805475551777467493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4743933203650367851644995 7115899805475551777467493)
                    ·
                      refine ⟨1334231213526665958275155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7115899805475551777467493 1334231213526665958275155)
                      ·
                        rfl

theorem cell23_2598406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2598406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598406 prefixEnd_2598406 := by exact prefixLift 2598406
  have htrace : WordTrace (prefixWord ++ tailWord_2598406) baseStart_2598406 baseEnd_2598406 := by
    simpa [prefixWord, tailWord_2598406, baseEnd_2598406] using wordTrace_append hprefix tailTrace_2598406
  have hstable : (prefixWord ++ tailWord_2598406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598406).length < 2 ^ (prefixWord ++ tailWord_2598406).sum := by decide
  have hdescent : baseEnd_2598406 < baseStart_2598406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598535 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2598535 : Nat := 118140960795 + 2598535 * 2 ^ 59
def prefixEnd_2598535 : Nat := 4983230072969 + 3 ^ 40 * 2598535 * 2
def baseEnd_2598535 : Nat := 1334297452531095953562061

theorem tailTrace_2598535 : CollatzResearch.WordTrace tailWord_2598535 prefixEnd_2598535 1334297452531095953562061 := by
  unfold tailWord_2598535
  simp only [CollatzResearch.WordTrace]
  refine ⟨94776357640958964290829059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63184238427305976193886039 94776357640958964290829059)
  ·
    refine ⟨142164536461438446436243589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94776357640958964290829059 142164536461438446436243589)
    ·
      refine ⟨26655850586519708706795673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142164536461438446436243589 26655850586519708706795673)
      ·
        refine ⟨19991887939889781530096755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26655850586519708706795673 19991887939889781530096755)
        ·
          refine ⟨29987831909834672295145133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19991887939889781530096755 29987831909834672295145133)
          ·
            refine ⟨11245436966188002110679425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29987831909834672295145133 11245436966188002110679425)
            ·
              refine ⟨8434077724641001583009569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11245436966188002110679425 8434077724641001583009569)
              ·
                refine ⟨6325558293480751187257177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8434077724641001583009569 6325558293480751187257177)
                ·
                  refine ⟨4744168720110563390442883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6325558293480751187257177 4744168720110563390442883)
                  ·
                    refine ⟨7116253080165845085664325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744168720110563390442883 7116253080165845085664325)
                    ·
                      refine ⟨1334297452531095953562061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7116253080165845085664325 1334297452531095953562061)
                      ·
                        rfl

theorem cell23_2598535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2598535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598535 prefixEnd_2598535 := by exact prefixLift 2598535
  have htrace : WordTrace (prefixWord ++ tailWord_2598535) baseStart_2598535 baseEnd_2598535 := by
    simpa [prefixWord, tailWord_2598535, baseEnd_2598535] using wordTrace_append hprefix tailTrace_2598535
  have hstable : (prefixWord ++ tailWord_2598535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598535).length < 2 ^ (prefixWord ++ tailWord_2598535).sum := by decide
  have hdescent : baseEnd_2598535 < baseStart_2598535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598536 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 5]
def baseStart_2598536 : Nat := 118140960795 + 2598536 * 2 ^ 59
def prefixEnd_2598536 : Nat := 4983230072969 + 3 ^ 40 * 2598536 * 2
def baseEnd_2598536 : Nat := 148255329556861161072173

theorem tailTrace_2598536 : CollatzResearch.WordTrace tailWord_2598536 prefixEnd_2598536 148255329556861161072173 := by
  unfold tailWord_2598536
  simp only [CollatzResearch.WordTrace]
  refine ⟨47388197056977670730807731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63184262742636894307743641 47388197056977670730807731)
  ·
    refine ⟨71082295585466506096211597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47388197056977670730807731 71082295585466506096211597)
    ·
      refine ⟨26655860844549939786079349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71082295585466506096211597 26655860844549939786079349)
      ·
        refine ⟨2498986954176556854944939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26655860844549939786079349 2498986954176556854944939)
        ·
          refine ⟨3748480431264835282417409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498986954176556854944939 3748480431264835282417409)
          ·
            refine ⟨2811360323448626461813057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3748480431264835282417409 2811360323448626461813057)
            ·
              refine ⟨2108520242586469846359793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811360323448626461813057 2108520242586469846359793)
              ·
                refine ⟨1581390181939852384769845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108520242586469846359793 1581390181939852384769845)
                ·
                  refine ⟨148255329556861161072173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1581390181939852384769845 148255329556861161072173)
                  ·
                    rfl

theorem cell23_2598536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 5].length) (baseStart_2598536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598536 prefixEnd_2598536 := by exact prefixLift 2598536
  have htrace : WordTrace (prefixWord ++ tailWord_2598536) baseStart_2598536 baseEnd_2598536 := by
    simpa [prefixWord, tailWord_2598536, baseEnd_2598536] using wordTrace_append hprefix tailTrace_2598536
  have hstable : (prefixWord ++ tailWord_2598536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598536).length < 2 ^ (prefixWord ++ tailWord_2598536).sum := by decide
  have hdescent : baseEnd_2598536 < baseStart_2598536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598552 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2598552 : Nat := 118140960795 + 2598552 * 2 ^ 59
def prefixEnd_2598552 : Nat := 4983230072969 + 3 ^ 40 * 2598552 * 2
def baseEnd_2598552 : Nat := 1334306181702222387049483

theorem tailTrace_2598552 : CollatzResearch.WordTrace tailWord_2598552 prefixEnd_2598552 1334306181702222387049483 := by
  unfold tailWord_2598552
  simp only [CollatzResearch.WordTrace]
  refine ⟨47388488840948688097098955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63184651787931584129465273 47388488840948688097098955)
  ·
    refine ⟨71082733261423032145648433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47388488840948688097098955 71082733261423032145648433)
    ·
      refine ⟨53312049946067274109236325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71082733261423032145648433 53312049946067274109236325)
      ·
        refine ⟨9996009364887613895481811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53312049946067274109236325 9996009364887613895481811)
        ·
          refine ⟨14994014047331420843222717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9996009364887613895481811 14994014047331420843222717)
          ·
            refine ⟨5622755267749282816208519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14994014047331420843222717 5622755267749282816208519)
            ·
              refine ⟨8434132901623924224312779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622755267749282816208519 8434132901623924224312779)
              ·
                refine ⟨12651199352435886336469169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434132901623924224312779 12651199352435886336469169)
                ·
                  refine ⟨9488399514326914752351877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12651199352435886336469169 9488399514326914752351877)
                  ·
                    refine ⟨1779074908936296516065977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9488399514326914752351877 1779074908936296516065977)
                    ·
                      refine ⟨1334306181702222387049483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779074908936296516065977 1334306181702222387049483)
                      ·
                        rfl

theorem cell23_2598552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2598552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598552 prefixEnd_2598552 := by exact prefixLift 2598552
  have htrace : WordTrace (prefixWord ++ tailWord_2598552) baseStart_2598552 baseEnd_2598552 := by
    simpa [prefixWord, tailWord_2598552, baseEnd_2598552] using wordTrace_append hprefix tailTrace_2598552
  have hstable : (prefixWord ++ tailWord_2598552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598552).length < 2 ^ (prefixWord ++ tailWord_2598552).sum := by decide
  have hdescent : baseEnd_2598552 < baseStart_2598552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598582 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2598582 : Nat := 118140960795 + 2598582 * 2 ^ 59
def prefixEnd_2598582 : Nat := 4983230072969 + 3 ^ 40 * 2598582 * 2
def baseEnd_2598582 : Nat := 1334321586121857269674345

theorem tailTrace_2598582 : CollatzResearch.WordTrace tailWord_2598582 prefixEnd_2598582 1334321586121857269674345 := by
  unfold tailWord_2598582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923629491986793207361875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63185381247859127545193333 5923629491986793207361875)
  ·
    refine ⟨8885444237980189811042813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923629491986793207361875 8885444237980189811042813)
    ·
      refine ⟨3332041589242571179141055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8885444237980189811042813 3332041589242571179141055)
      ·
        refine ⟨4998062383863856768711583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3332041589242571179141055 4998062383863856768711583)
        ·
          refine ⟨7497093575795785153067375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998062383863856768711583 7497093575795785153067375)
          ·
            refine ⟨11245640363693677729601063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497093575795785153067375 11245640363693677729601063)
            ·
              refine ⟨16868460545540516594401595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11245640363693677729601063 16868460545540516594401595)
              ·
                refine ⟨25302690818310774891602393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16868460545540516594401595 25302690818310774891602393)
                ·
                  refine ⟨18977018113733081168701795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25302690818310774891602393 18977018113733081168701795)
                  ·
                    refine ⟨28465527170599621753052693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18977018113733081168701795 28465527170599621753052693)
                    ·
                      refine ⟨1334321586121857269674345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28465527170599621753052693 1334321586121857269674345)
                      ·
                        rfl

theorem cell23_2598582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2598582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598582 prefixEnd_2598582 := by exact prefixLift 2598582
  have htrace : WordTrace (prefixWord ++ tailWord_2598582) baseStart_2598582 baseEnd_2598582 := by
    simpa [prefixWord, tailWord_2598582, baseEnd_2598582] using wordTrace_append hprefix tailTrace_2598582
  have hstable : (prefixWord ++ tailWord_2598582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598582).length < 2 ^ (prefixWord ++ tailWord_2598582).sum := by decide
  have hdescent : baseEnd_2598582 < baseStart_2598582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598608 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_2598608 : Nat := 118140960795 + 2598608 * 2 ^ 59
def prefixEnd_2598608 : Nat := 4983230072969 + 3 ^ 40 * 2598608 * 2
def baseEnd_2598608 : Nat := 1334334936618874167949225

theorem tailTrace_2598608 : CollatzResearch.WordTrace tailWord_2598608 prefixEnd_2598608 1334334936618874167949225 := by
  unfold tailWord_2598608
  simp only [CollatzResearch.WordTrace]
  refine ⟨47389510084847248879118239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63186013446462998505490985 47389510084847248879118239)
  ·
    refine ⟨71084265127270873318677359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47389510084847248879118239 71084265127270873318677359)
    ·
      refine ⟨106626397690906309978016039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71084265127270873318677359 106626397690906309978016039)
      ·
        refine ⟨159939596536359464967024059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106626397690906309978016039 159939596536359464967024059)
        ·
          refine ⟨239909394804539197450536089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159939596536359464967024059 239909394804539197450536089)
          ·
            refine ⟨179932046103404398087902067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239909394804539197450536089 179932046103404398087902067)
            ·
              refine ⟨269898069155106597131853101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179932046103404398087902067 269898069155106597131853101)
              ·
                refine ⟨101211775933164973924444913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269898069155106597131853101 101211775933164973924444913)
                ·
                  refine ⟨75908831949873730443333685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101211775933164973924444913 75908831949873730443333685)
                  ·
                    refine ⟨7116452995300662229062533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75908831949873730443333685 7116452995300662229062533)
                    ·
                      refine ⟨1334334936618874167949225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7116452995300662229062533 1334334936618874167949225)
                      ·
                        rfl

theorem cell23_2598608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_2598608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598608 prefixEnd_2598608 := by exact prefixLift 2598608
  have htrace : WordTrace (prefixWord ++ tailWord_2598608) baseStart_2598608 baseEnd_2598608 := by
    simpa [prefixWord, tailWord_2598608, baseEnd_2598608] using wordTrace_append hprefix tailTrace_2598608
  have hstable : (prefixWord ++ tailWord_2598608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598608).length < 2 ^ (prefixWord ++ tailWord_2598608).sum := by decide
  have hdescent : baseEnd_2598608 < baseStart_2598608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598635 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 4, 4]
def baseStart_2598635 : Nat := 118140960795 + 2598635 * 2 ^ 59
def prefixEnd_2598635 : Nat := 4983230072969 + 3 ^ 40 * 2598635 * 2
def baseEnd_2598635 : Nat := 444782933532181854103867

theorem tailTrace_2598635 : CollatzResearch.WordTrace tailWord_2598635 prefixEnd_2598635 444782933532181854103867 := by
  unfold tailWord_2598635
  simp only [CollatzResearch.WordTrace]
  refine ⟨94780004940596681369469359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63186669960397787579646239 94780004940596681369469359)
  ·
    refine ⟨142170007410895022054204039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94780004940596681369469359 142170007410895022054204039)
    ·
      refine ⟨213255011116342533081306059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142170007410895022054204039 213255011116342533081306059)
      ·
        refine ⟨319882516674513799621959089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213255011116342533081306059 319882516674513799621959089)
        ·
          refine ⟨239911887505885349716469317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319882516674513799621959089 239911887505885349716469317)
          ·
            refine ⟨44983478907353503071837997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239911887505885349716469317 44983478907353503071837997)
            ·
              refine ⟨16868804590257563651939249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44983478907353503071837997 16868804590257563651939249)
              ·
                refine ⟨12651603442693172738954437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16868804590257563651939249 12651603442693172738954437)
                ·
                  refine ⟨2372175645504969888553957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12651603442693172738954437 2372175645504969888553957)
                  ·
                    refine ⟨444782933532181854103867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372175645504969888553957 444782933532181854103867)
                    ·
                      rfl

theorem cell23_2598635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 4].length) (baseStart_2598635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598635 prefixEnd_2598635 := by exact prefixLift 2598635
  have htrace : WordTrace (prefixWord ++ tailWord_2598635) baseStart_2598635 baseEnd_2598635 := by
    simpa [prefixWord, tailWord_2598635, baseEnd_2598635] using wordTrace_append hprefix tailTrace_2598635
  have hstable : (prefixWord ++ tailWord_2598635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598635).length < 2 ^ (prefixWord ++ tailWord_2598635).sum := by decide
  have hdescent : baseEnd_2598635 < baseStart_2598635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598642 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2598642 : Nat := 118140960795 + 2598642 * 2 ^ 59
def prefixEnd_2598642 : Nat := 4983230072969 + 3 ^ 40 * 2598642 * 2
def baseEnd_2598642 : Nat := 1334352394961127034924069

theorem tailTrace_2598642 : CollatzResearch.WordTrace tailWord_2598642 prefixEnd_2598642 1334352394961127034924069 := by
  unfold tailWord_2598642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23695065062892830391243545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63186840167714214376649453 23695065062892830391243545)
  ·
    refine ⟨17771298797169622793432659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23695065062892830391243545 17771298797169622793432659)
    ·
      refine ⟨26656948195754434190148989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17771298797169622793432659 26656948195754434190148989)
      ·
        refine ⟨9996355573407912821305871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26656948195754434190148989 9996355573407912821305871)
        ·
          refine ⟨14994533360111869231958807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9996355573407912821305871 14994533360111869231958807)
          ·
            refine ⟨22491800040167803847938211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14994533360111869231958807 22491800040167803847938211)
            ·
              refine ⟨33737700060251705771907317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22491800040167803847938211 33737700060251705771907317)
              ·
                refine ⟨3162909380648597416116311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33737700060251705771907317 3162909380648597416116311)
                ·
                  refine ⟨4744364070972896124174467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162909380648597416116311 4744364070972896124174467)
                  ·
                    refine ⟨7116546106459344186261701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744364070972896124174467 7116546106459344186261701)
                    ·
                      refine ⟨1334352394961127034924069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7116546106459344186261701 1334352394961127034924069)
                      ·
                        rfl

theorem cell23_2598642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2598642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598642 prefixEnd_2598642 := by exact prefixLift 2598642
  have htrace : WordTrace (prefixWord ++ tailWord_2598642) baseStart_2598642 baseEnd_2598642 := by
    simpa [prefixWord, tailWord_2598642, baseEnd_2598642] using wordTrace_append hprefix tailTrace_2598642
  have hstable : (prefixWord ++ tailWord_2598642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598642).length < 2 ^ (prefixWord ++ tailWord_2598642).sum := by decide
  have hdescent : baseEnd_2598642 < baseStart_2598642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598652 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_2598652 : Nat := 118140960795 + 2598652 * 2 ^ 59
def prefixEnd_2598652 : Nat := 4983230072969 + 3 ^ 40 * 2598652 * 2
def baseEnd_2598652 : Nat := 444785843255890665266341

theorem tailTrace_2598652 : CollatzResearch.WordTrace tailWord_2598652 prefixEnd_2598652 444785843255890665266341 := by
  unfold tailWord_2598652
  simp only [CollatzResearch.WordTrace]
  refine ⟨47390312490767546636419105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63187083321023395515225473 47390312490767546636419105)
  ·
    refine ⟨35542734368075659977314329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47390312490767546636419105 35542734368075659977314329)
    ·
      refine ⟨26657050776056744982985747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35542734368075659977314329 26657050776056744982985747)
      ·
        refine ⟨39985576164085117474478621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26657050776056744982985747 39985576164085117474478621)
        ·
          refine ⟨14994591061531919052929483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39985576164085117474478621 14994591061531919052929483)
          ·
            refine ⟨22491886592297878579394225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14994591061531919052929483 22491886592297878579394225)
            ·
              refine ⟨16868914944223408934545669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22491886592297878579394225 16868914944223408934545669)
              ·
                refine ⟨3162921552041889175227313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16868914944223408934545669 3162921552041889175227313)
                ·
                  refine ⟨2372191164031416881420485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162921552041889175227313 2372191164031416881420485)
                  ·
                    refine ⟨444785843255890665266341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372191164031416881420485 444785843255890665266341)
                    ·
                      rfl

theorem cell23_2598652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_2598652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598652 prefixEnd_2598652 := by exact prefixLift 2598652
  have htrace : WordTrace (prefixWord ++ tailWord_2598652) baseStart_2598652 baseEnd_2598652 := by
    simpa [prefixWord, tailWord_2598652, baseEnd_2598652] using wordTrace_append hprefix tailTrace_2598652
  have hstable : (prefixWord ++ tailWord_2598652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598652).length < 2 ^ (prefixWord ++ tailWord_2598652).sum := by decide
  have hdescent : baseEnd_2598652 < baseStart_2598652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598659 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 3, 2, 2]
def baseStart_2598659 : Nat := 118140960795 + 2598659 * 2 ^ 59
def prefixEnd_2598659 : Nat := 4983230072969 + 3 ^ 40 * 2598659 * 2
def baseEnd_2598659 : Nat := 1334361124132253468411491

theorem tailTrace_2598659 : CollatzResearch.WordTrace tailWord_2598659 prefixEnd_2598659 1334361124132253468411491 := by
  unfold tailWord_2598659
  simp only [CollatzResearch.WordTrace]
  refine ⟨94780880292509733468343031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63187253528339822312228687 94780880292509733468343031)
  ·
    refine ⟨142171320438764600202514547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94780880292509733468343031 142171320438764600202514547)
    ·
      refine ⟨213256980658146900303771821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142171320438764600202514547 213256980658146900303771821)
      ·
        refine ⟨79971367746805087613914433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213256980658146900303771821 79971367746805087613914433)
        ·
          refine ⟨59978525810103815710435825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79971367746805087613914433 59978525810103815710435825)
          ·
            refine ⟨44983894357577861782826869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59978525810103815710435825 44983894357577861782826869)
            ·
              refine ⟨4217240096022924542140019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44983894357577861782826869 4217240096022924542140019)
              ·
                refine ⟨6325860144034386813210029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217240096022924542140019 6325860144034386813210029)
                ·
                  refine ⟨2372197554012895054953761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6325860144034386813210029 2372197554012895054953761)
                  ·
                    refine ⟨1779148165509671291215321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2372197554012895054953761 1779148165509671291215321)
                    ·
                      refine ⟨1334361124132253468411491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779148165509671291215321 1334361124132253468411491)
                      ·
                        rfl

theorem cell23_2598659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_2598659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598659 prefixEnd_2598659 := by exact prefixLift 2598659
  have htrace : WordTrace (prefixWord ++ tailWord_2598659) baseStart_2598659 baseEnd_2598659 := by
    simpa [prefixWord, tailWord_2598659, baseEnd_2598659] using wordTrace_append hprefix tailTrace_2598659
  have hstable : (prefixWord ++ tailWord_2598659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598659).length < 2 ^ (prefixWord ++ tailWord_2598659).sum := by decide
  have hdescent : baseEnd_2598659 < baseStart_2598659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598679 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2598679 : Nat := 118140960795 + 2598679 * 2 ^ 59
def prefixEnd_2598679 : Nat := 4983230072969 + 3 ^ 40 * 2598679 * 2
def baseEnd_2598679 : Nat := 1334371393745343390161399

theorem tailTrace_2598679 : CollatzResearch.WordTrace tailWord_2598679 prefixEnd_2598679 1334371393745343390161399 := by
  unfold tailWord_2598679
  simp only [CollatzResearch.WordTrace]
  refine ⟨94781609752437276884071091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63187739834958184589380727 94781609752437276884071091)
  ·
    refine ⟨142172414628655915326106637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94781609752437276884071091 142172414628655915326106637)
    ·
      refine ⟨53314655485745968247289989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142172414628655915326106637 53314655485745968247289989)
      ·
        refine ⟨9996497903577369046366873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53314655485745968247289989 9996497903577369046366873)
        ·
          refine ⟨7497373427683026784775155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996497903577369046366873 7497373427683026784775155)
          ·
            refine ⟨11246060141524540177162733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497373427683026784775155 11246060141524540177162733)
            ·
              refine ⟨4217272553071702566436025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11246060141524540177162733 4217272553071702566436025)
              ·
                refine ⟨3162954414803776924827019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217272553071702566436025 3162954414803776924827019)
                ·
                  refine ⟨4744431622205665387240529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162954414803776924827019 4744431622205665387240529)
                  ·
                    refine ⟨3558323716654249040430397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744431622205665387240529 3558323716654249040430397)
                    ·
                      refine ⟨1334371393745343390161399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558323716654249040430397 1334371393745343390161399)
                      ·
                        rfl

theorem cell23_2598679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2598679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598679 prefixEnd_2598679 := by exact prefixLift 2598679
  have htrace : WordTrace (prefixWord ++ tailWord_2598679) baseStart_2598679 baseEnd_2598679 := by
    simpa [prefixWord, tailWord_2598679, baseEnd_2598679] using wordTrace_append hprefix tailTrace_2598679
  have hstable : (prefixWord ++ tailWord_2598679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598679).length < 2 ^ (prefixWord ++ tailWord_2598679).sum := by decide
  have hdescent : baseEnd_2598679 < baseStart_2598679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598686 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2598686 : Nat := 118140960795 + 2598686 * 2 ^ 59
def prefixEnd_2598686 : Nat := 4983230072969 + 3 ^ 40 * 2598686 * 2
def baseEnd_2598686 : Nat := 444791662703308287591289

theorem tailTrace_2598686 : CollatzResearch.WordTrace tailWord_2598686 prefixEnd_2598686 444791662703308287591289 := by
  unfold tailWord_2598686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11847733132926489634946989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63187910042274611386383941 11847733132926489634946989)
  ·
    refine ⟨4442899924847433613105121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11847733132926489634946989 4442899924847433613105121)
    ·
      refine ⟨3332174943635575209828841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4442899924847433613105121 3332174943635575209828841)
      ·
        refine ⟨2499131207726681407371631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3332174943635575209828841 2499131207726681407371631)
        ·
          refine ⟨3748696811590022111057447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499131207726681407371631 3748696811590022111057447)
          ·
            refine ⟨5623045217385033166586171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748696811590022111057447 5623045217385033166586171)
            ·
              refine ⟨8434567826077549749879257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623045217385033166586171 8434567826077549749879257)
              ·
                refine ⟨6325925869558162312409443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8434567826077549749879257 6325925869558162312409443)
                ·
                  refine ⟨9488888804337243468614165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325925869558162312409443 9488888804337243468614165)
                  ·
                    refine ⟨444791662703308287591289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9488888804337243468614165 444791662703308287591289)
                    ·
                      rfl

theorem cell23_2598686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2598686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598686 prefixEnd_2598686 := by exact prefixLift 2598686
  have htrace : WordTrace (prefixWord ++ tailWord_2598686) baseStart_2598686 baseEnd_2598686 := by
    simpa [prefixWord, tailWord_2598686, baseEnd_2598686] using wordTrace_append hprefix tailTrace_2598686
  have hstable : (prefixWord ++ tailWord_2598686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598686).length < 2 ^ (prefixWord ++ tailWord_2598686).sum := by decide
  have hdescent : baseEnd_2598686 < baseStart_2598686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598692 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_2598692 : Nat := 118140960795 + 2598692 * 2 ^ 59
def prefixEnd_2598692 : Nat := 4983230072969 + 3 ^ 40 * 2598692 * 2
def baseEnd_2598692 : Nat := 1334378068993851839298839

theorem tailTrace_2598692 : CollatzResearch.WordTrace tailWord_2598692 prefixEnd_2598692 1334378068993851839298839 := by
  unfold tailWord_2598692
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391041950695090052147165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63188055934260120069529553 47391041950695090052147165)
  ·
    refine ⟨17771640731510658769555187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47391041950695090052147165 17771640731510658769555187)
    ·
      refine ⟨26657461097265988154332781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17771640731510658769555187 26657461097265988154332781)
      ·
        refine ⟨9996547911474745557874793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26657461097265988154332781 9996547911474745557874793)
        ·
          refine ⟨7497410933606059168406095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996547911474745557874793 7497410933606059168406095)
          ·
            refine ⟨11246116400409088752609143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497410933606059168406095 11246116400409088752609143)
            ·
              refine ⟨16869174600613633128913715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11246116400409088752609143 16869174600613633128913715)
              ·
                refine ⟨25303761900920449693370573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16869174600613633128913715 25303761900920449693370573)
                ·
                  refine ⟨9488910712845168635013965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25303761900920449693370573 9488910712845168635013965)
                  ·
                    refine ⟨3558341517316938238130237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9488910712845168635013965 3558341517316938238130237)
                    ·
                      refine ⟨1334378068993851839298839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558341517316938238130237 1334378068993851839298839)
                      ·
                        rfl

theorem cell23_2598692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_2598692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598692 prefixEnd_2598692 := by exact prefixLift 2598692
  have htrace : WordTrace (prefixWord ++ tailWord_2598692) baseStart_2598692 baseEnd_2598692 := by
    simpa [prefixWord, tailWord_2598692, baseEnd_2598692] using wordTrace_append hprefix tailTrace_2598692
  have hstable : (prefixWord ++ tailWord_2598692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598692).length < 2 ^ (prefixWord ++ tailWord_2598692).sum := by decide
  have hdescent : baseEnd_2598692 < baseStart_2598692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598696 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_2598696 : Nat := 118140960795 + 2598696 * 2 ^ 59
def prefixEnd_2598696 : Nat := 4983230072969 + 3 ^ 40 * 2598696 * 2
def baseEnd_2598696 : Nat := 1334380122916469823648821

theorem tailTrace_2598696 : CollatzResearch.WordTrace tailWord_2598696 prefixEnd_2598696 1334380122916469823648821 := by
  unfold tailWord_2598696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391114896687844393719971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63188153195583792524959961 47391114896687844393719971)
  ·
    refine ⟨71086672345031766590579957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47391114896687844393719971 71086672345031766590579957)
    ·
      refine ⟨6664375532346728117866871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71086672345031766590579957 6664375532346728117866871)
      ·
        refine ⟨9996563298520092176800307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6664375532346728117866871 9996563298520092176800307)
        ·
          refine ⟨14994844947780138265200461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9996563298520092176800307 14994844947780138265200461)
          ·
            refine ⟨5623066855417551849450173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14994844947780138265200461 5623066855417551849450173)
            ·
              refine ⟨2108650070781581943543815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5623066855417551849450173 2108650070781581943543815)
              ·
                refine ⟨3162975106172372915315723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108650070781581943543815 3162975106172372915315723)
                ·
                  refine ⟨4744462659258559372973585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162975106172372915315723 4744462659258559372973585)
                  ·
                    refine ⟨3558346994443919529730189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744462659258559372973585 3558346994443919529730189)
                    ·
                      refine ⟨1334380122916469823648821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558346994443919529730189 1334380122916469823648821)
                      ·
                        rfl

theorem cell23_2598696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_2598696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598696 prefixEnd_2598696 := by exact prefixLift 2598696
  have htrace : WordTrace (prefixWord ++ tailWord_2598696) baseStart_2598696 baseEnd_2598696 := by
    simpa [prefixWord, tailWord_2598696, baseEnd_2598696] using wordTrace_append hprefix tailTrace_2598696
  have hstable : (prefixWord ++ tailWord_2598696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598696).length < 2 ^ (prefixWord ++ tailWord_2598696).sum := by decide
  have hdescent : baseEnd_2598696 < baseStart_2598696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598710 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2598710 : Nat := 118140960795 + 2598710 * 2 ^ 59
def prefixEnd_2598710 : Nat := 4983230072969 + 3 ^ 40 * 2598710 * 2
def baseEnd_2598710 : Nat := 1334387311645632768873757

theorem tailTrace_2598710 : CollatzResearch.WordTrace tailWord_2598710 prefixEnd_2598710 1334387311645632768873757 := by
  unfold tailWord_2598710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923921275957810573653099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63188493610216646118966389 5923921275957810573653099)
  ·
    refine ⟨8885881913936715860479649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923921275957810573653099 8885881913936715860479649)
    ·
      refine ⟨6664411435452536895359737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8885881913936715860479649 6664411435452536895359737)
      ·
        refine ⟨4998308576589402671519803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6664411435452536895359737 4998308576589402671519803)
        ·
          refine ⟨7497462864884104007279705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998308576589402671519803 7497462864884104007279705)
          ·
            refine ⟨5623097148663078005459779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7497462864884104007279705 5623097148663078005459779)
            ·
              refine ⟨8434645722994617008189669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623097148663078005459779 8434645722994617008189669)
              ·
                refine ⟨1581496073061490689035563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8434645722994617008189669 1581496073061490689035563)
                ·
                  refine ⟨2372244109592236033553345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581496073061490689035563 2372244109592236033553345)
                  ·
                    refine ⟨1779183082194177025165009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2372244109592236033553345 1779183082194177025165009)
                    ·
                      refine ⟨1334387311645632768873757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779183082194177025165009 1334387311645632768873757)
                      ·
                        rfl

theorem cell23_2598710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2598710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598710 prefixEnd_2598710 := by exact prefixLift 2598710
  have htrace : WordTrace (prefixWord ++ tailWord_2598710) baseStart_2598710 baseEnd_2598710 := by
    simpa [prefixWord, tailWord_2598710, baseEnd_2598710] using wordTrace_append hprefix tailTrace_2598710
  have hstable : (prefixWord ++ tailWord_2598710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598710).length < 2 ^ (prefixWord ++ tailWord_2598710).sum := by decide
  have hdescent : baseEnd_2598710 < baseStart_2598710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598725 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_2598725 : Nat := 118140960795 + 2598725 * 2 ^ 59
def prefixEnd_2598725 : Nat := 4983230072969 + 3 ^ 40 * 2598725 * 2
def baseEnd_2598725 : Nat := 444798337951816736728729

theorem tailTrace_2598725 : CollatzResearch.WordTrace tailWord_2598725 prefixEnd_2598725 444798337951816736728729 := by
  unfold tailWord_2598725
  simp only [CollatzResearch.WordTrace]
  refine ⟨94783287510270626740245629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63188858340180417826830419 94783287510270626740245629)
  ·
    refine ⟨35543732816351485027592111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94783287510270626740245629 35543732816351485027592111)
    ·
      refine ⟨53315599224527227541388167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35543732816351485027592111 53315599224527227541388167)
      ·
        refine ⟨79973398836790841312082251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53315599224527227541388167 79973398836790841312082251)
        ·
          refine ⟨119960098255186261968123377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79973398836790841312082251 119960098255186261968123377)
          ·
            refine ⟨89970073691389696476092533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119960098255186261968123377 89970073691389696476092533)
            ·
              refine ⟨8434694408567784044633675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89970073691389696476092533 8434694408567784044633675)
              ·
                refine ⟨12652041612851676066950513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434694408567784044633675 12652041612851676066950513)
                ·
                  refine ⟨9489031209638757050212885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12652041612851676066950513 9489031209638757050212885)
                  ·
                    refine ⟨444798337951816736728729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9489031209638757050212885 444798337951816736728729)
                    ·
                      rfl

theorem cell23_2598725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_2598725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598725 prefixEnd_2598725 := by exact prefixLift 2598725
  have htrace : WordTrace (prefixWord ++ tailWord_2598725) baseStart_2598725 baseEnd_2598725 := by
    simpa [prefixWord, tailWord_2598725, baseEnd_2598725] using wordTrace_append hprefix tailTrace_2598725
  have hstable : (prefixWord ++ tailWord_2598725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598725).length < 2 ^ (prefixWord ++ tailWord_2598725).sum := by decide
  have hdescent : baseEnd_2598725 < baseStart_2598725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598726 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2598726 : Nat := 118140960795 + 2598726 * 2 ^ 59
def prefixEnd_2598726 : Nat := 4983230072969 + 3 ^ 40 * 2598726 * 2
def baseEnd_2598726 : Nat := 1334395527336104706273683

theorem tailTrace_2598726 : CollatzResearch.WordTrace tailWord_2598726 prefixEnd_2598726 1334395527336104706273683 := by
  unfold tailWord_2598726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961978874477093872219751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63188882655511335940688021 2961978874477093872219751)
  ·
    refine ⟨4442968311715640808329627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2961978874477093872219751 4442968311715640808329627)
    ·
      refine ⟨6664452467573461212494441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4442968311715640808329627 6664452467573461212494441)
      ·
        refine ⟨4998339350680095909370831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6664452467573461212494441 4998339350680095909370831)
        ·
          refine ⟨7497509026020143864056247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998339350680095909370831 7497509026020143864056247)
          ·
            refine ⟨11246263539030215796084371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497509026020143864056247 11246263539030215796084371)
            ·
              refine ⟨16869395308545323694126557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11246263539030215796084371 16869395308545323694126557)
              ·
                refine ⟨6326023240704496385297459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16869395308545323694126557 6326023240704496385297459)
                ·
                  refine ⟨9489034861056744577946189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6326023240704496385297459 9489034861056744577946189)
                  ·
                    refine ⟨3558388072896279216729821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9489034861056744577946189 3558388072896279216729821)
                    ·
                      refine ⟨1334395527336104706273683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558388072896279216729821 1334395527336104706273683)
                      ·
                        rfl

theorem cell23_2598726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2598726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598726 prefixEnd_2598726 := by exact prefixLift 2598726
  have htrace : WordTrace (prefixWord ++ tailWord_2598726) baseStart_2598726 baseEnd_2598726 := by
    simpa [prefixWord, tailWord_2598726, baseEnd_2598726] using wordTrace_append hprefix tailTrace_2598726
  have hstable : (prefixWord ++ tailWord_2598726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598726).length < 2 ^ (prefixWord ++ tailWord_2598726).sum := by decide
  have hdescent : baseEnd_2598726 < baseStart_2598726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598745 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_2598745 : Nat := 118140960795 + 2598745 * 2 ^ 59
def prefixEnd_2598745 : Nat := 4983230072969 + 3 ^ 40 * 2598745 * 2
def baseEnd_2598745 : Nat := 1334405283468540131936095

theorem tailTrace_2598745 : CollatzResearch.WordTrace tailWord_2598745 prefixEnd_2598745 1334405283468540131936095 := by
  unfold tailWord_2598745
  simp only [CollatzResearch.WordTrace]
  refine ⟨94784016970198170155973689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63189344646798780103982459 94784016970198170155973689)
  ·
    refine ⟨71088012727648627616980267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94784016970198170155973689 71088012727648627616980267)
    ·
      refine ⟨106632019091472941425470401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71088012727648627616980267 106632019091472941425470401)
      ·
        refine ⟨79974014318604706069102801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106632019091472941425470401 79974014318604706069102801)
        ·
          refine ⟨59980510738953529551827101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79974014318604706069102801 59980510738953529551827101)
          ·
            refine ⟨22492691527107573581935163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59980510738953529551827101 22492691527107573581935163)
            ·
              refine ⟨33739037290661360372902745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22492691527107573581935163 33739037290661360372902745)
              ·
                refine ⟨25304277967996020279677059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33739037290661360372902745 25304277967996020279677059)
                ·
                  refine ⟨37956416951994030419515589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25304277967996020279677059 37956416951994030419515589)
                  ·
                    refine ⟨7116828178498880703659173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37956416951994030419515589 7116828178498880703659173)
                    ·
                      refine ⟨1334405283468540131936095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7116828178498880703659173 1334405283468540131936095)
                      ·
                        rfl

theorem cell23_2598745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_2598745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598745 prefixEnd_2598745 := by exact prefixLift 2598745
  have htrace : WordTrace (prefixWord ++ tailWord_2598745) baseStart_2598745 baseEnd_2598745 := by
    simpa [prefixWord, tailWord_2598745, baseEnd_2598745] using wordTrace_append hprefix tailTrace_2598745
  have hstable : (prefixWord ++ tailWord_2598745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598745).length < 2 ^ (prefixWord ++ tailWord_2598745).sum := by decide
  have hdescent : baseEnd_2598745 < baseStart_2598745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598795 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_2598795 : Nat := 118140960795 + 2598795 * 2 ^ 59
def prefixEnd_2598795 : Nat := 4983230072969 + 3 ^ 40 * 2598795 * 2
def baseEnd_2598795 : Nat := 1334430957501264936310865

theorem tailTrace_2598795 : CollatzResearch.WordTrace tailWord_2598795 prefixEnd_2598795 1334430957501264936310865 := by
  unfold tailWord_2598795
  simp only [CollatzResearch.WordTrace]
  refine ⟨94785840620017028695293839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63190560413344685796862559 94785840620017028695293839)
  ·
    refine ⟨142178760930025543042940759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94785840620017028695293839 142178760930025543042940759)
    ·
      refine ⟨213268141395038314564411139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142178760930025543042940759 213268141395038314564411139)
      ·
        refine ⟨319902212092557471846616709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213268141395038314564411139 319902212092557471846616709)
        ·
          refine ⟨59981664767354525971240633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319902212092557471846616709 59981664767354525971240633)
          ·
            refine ⟨44986248575515894478430475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59981664767354525971240633 44986248575515894478430475)
            ·
              refine ⟨67479372863273841717645713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44986248575515894478430475 67479372863273841717645713)
              ·
                refine ⟨50609529647455381288234285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67479372863273841717645713 50609529647455381288234285)
                ·
                  refine ⟨18978573617795767983087857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50609529647455381288234285 18978573617795767983087857)
                  ·
                    refine ⟨14233930213346825987315893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18978573617795767983087857 14233930213346825987315893)
                    ·
                      refine ⟨1334430957501264936310865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14233930213346825987315893 1334430957501264936310865)
                      ·
                        rfl

theorem cell23_2598795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_2598795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598795 prefixEnd_2598795 := by exact prefixLift 2598795
  have htrace : WordTrace (prefixWord ++ tailWord_2598795) baseStart_2598795 baseEnd_2598795 := by
    simpa [prefixWord, tailWord_2598795, baseEnd_2598795] using wordTrace_append hprefix tailTrace_2598795
  have hstable : (prefixWord ++ tailWord_2598795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598795).length < 2 ^ (prefixWord ++ tailWord_2598795).sum := by decide
  have hdescent : baseEnd_2598795 < baseStart_2598795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598825 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_2598825 : Nat := 118140960795 + 2598825 * 2 ^ 59
def prefixEnd_2598825 : Nat := 4983230072969 + 3 ^ 40 * 2598825 * 2
def baseEnd_2598825 : Nat := 1334446361920899818935727

theorem tailTrace_2598825 : CollatzResearch.WordTrace tailWord_2598825 prefixEnd_2598825 1334446361920899818935727 := by
  unfold tailWord_2598825
  simp only [CollatzResearch.WordTrace]
  refine ⟨94786934809908343818885929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63191289873272229212590619 94786934809908343818885929)
  ·
    refine ⟨71090201107431257864164447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94786934809908343818885929 71090201107431257864164447)
    ·
      refine ⟨106635301661146886796246671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71090201107431257864164447 106635301661146886796246671)
      ·
        refine ⟨159952952491720330194370007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106635301661146886796246671 159952952491720330194370007)
        ·
          refine ⟨239929428737580495291555011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159952952491720330194370007 239929428737580495291555011)
          ·
            refine ⟨359894143106370742937332517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239929428737580495291555011 359894143106370742937332517)
            ·
              refine ⟨67480151832444514300749847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 359894143106370742937332517 67480151832444514300749847)
              ·
                refine ⟨101220227748666771451124771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67480151832444514300749847 101220227748666771451124771)
                ·
                  refine ⟨151830341623000157176687157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101220227748666771451124771 151830341623000157176687157)
                  ·
                    refine ⟨14234094527156264735314421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151830341623000157176687157 14234094527156264735314421)
                    ·
                      refine ⟨1334446361920899818935727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14234094527156264735314421 1334446361920899818935727)
                      ·
                        rfl

theorem cell23_2598825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_2598825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598825 prefixEnd_2598825 := by exact prefixLift 2598825
  have htrace : WordTrace (prefixWord ++ tailWord_2598825) baseStart_2598825 baseEnd_2598825 := by
    simpa [prefixWord, tailWord_2598825, baseEnd_2598825] using wordTrace_append hprefix tailTrace_2598825
  have hstable : (prefixWord ++ tailWord_2598825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598825).length < 2 ^ (prefixWord ++ tailWord_2598825).sum := by decide
  have hdescent : baseEnd_2598825 < baseStart_2598825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598842 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_2598842 : Nat := 118140960795 + 2598842 * 2 ^ 59
def prefixEnd_2598842 : Nat := 4983230072969 + 3 ^ 40 * 2598842 * 2
def baseEnd_2598842 : Nat := 1334455091092026252423149

theorem tailTrace_2598842 : CollatzResearch.WordTrace tailWord_2598842 prefixEnd_2598842 1334455091092026252423149 := by
  unfold tailWord_2598842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23696888712711688930563695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63191703233897837148169853 23696888712711688930563695)
  ·
    refine ⟨35545333069067533395845543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23696888712711688930563695 35545333069067533395845543)
    ·
      refine ⟨53317999603601300093768315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35545333069067533395845543 53317999603601300093768315)
      ·
        refine ⟨79976999405401950140652473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53317999603601300093768315 79976999405401950140652473)
        ·
          refine ⟨59982749554051462605489355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79976999405401950140652473 59982749554051462605489355)
          ·
            refine ⟨89974124331077193908234033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59982749554051462605489355 89974124331077193908234033)
            ·
              refine ⟨67480593248307895431175525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89974124331077193908234033 67480593248307895431175525)
              ·
                refine ⟨12652611234057730393345411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67480593248307895431175525 12652611234057730393345411)
                ·
                  refine ⟨18978916851086595590018117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12652611234057730393345411 18978916851086595590018117)
                  ·
                    refine ⟨3558546909578736673128397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18978916851086595590018117 3558546909578736673128397)
                    ·
                      refine ⟨1334455091092026252423149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558546909578736673128397 1334455091092026252423149)
                      ·
                        rfl

theorem cell23_2598842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_2598842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598842 prefixEnd_2598842 := by exact prefixLift 2598842
  have htrace : WordTrace (prefixWord ++ tailWord_2598842) baseStart_2598842 baseEnd_2598842 := by
    simpa [prefixWord, tailWord_2598842, baseEnd_2598842] using wordTrace_append hprefix tailTrace_2598842
  have hstable : (prefixWord ++ tailWord_2598842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598842).length < 2 ^ (prefixWord ++ tailWord_2598842).sum := by decide
  have hdescent : baseEnd_2598842 < baseStart_2598842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598859 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 3]
def baseStart_2598859 : Nat := 118140960795 + 2598859 * 2 ^ 59
def prefixEnd_2598859 : Nat := 4983230072969 + 3 ^ 40 * 2598859 * 2
def baseEnd_2598859 : Nat := 1334463820263152685910571

theorem tailTrace_2598859 : CollatzResearch.WordTrace tailWord_2598859 prefixEnd_2598859 1334463820263152685910571 := by
  unfold tailWord_2598859
  simp only [CollatzResearch.WordTrace]
  refine ⟨94788174891785167625623631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63192116594523445083749087 94788174891785167625623631)
  ·
    refine ⟨142182262337677751438435447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94788174891785167625623631 142182262337677751438435447)
    ·
      refine ⟨213273393506516627157653171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142182262337677751438435447 213273393506516627157653171)
      ·
        refine ⟨319910090259774940736479757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213273393506516627157653171 319910090259774940736479757)
        ·
          refine ⟨119966283847415602776179909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319910090259774940736479757 119966283847415602776179909)
          ·
            refine ⟨22493678221390425520533733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119966283847415602776179909 22493678221390425520533733)
            ·
              refine ⟨4217564666510704785100075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22493678221390425520533733 4217564666510704785100075)
              ·
                refine ⟨6326346999766057177650113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217564666510704785100075 6326346999766057177650113)
                ·
                  refine ⟨4744760249824542883237585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6326346999766057177650113 4744760249824542883237585)
                  ·
                    refine ⟨3558570187368407162428189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744760249824542883237585 3558570187368407162428189)
                    ·
                      refine ⟨1334463820263152685910571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558570187368407162428189 1334463820263152685910571)
                      ·
                        rfl

theorem cell23_2598859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 3].length) (baseStart_2598859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598859 prefixEnd_2598859 := by exact prefixLift 2598859
  have htrace : WordTrace (prefixWord ++ tailWord_2598859) baseStart_2598859 baseEnd_2598859 := by
    simpa [prefixWord, tailWord_2598859, baseEnd_2598859] using wordTrace_append hprefix tailTrace_2598859
  have hstable : (prefixWord ++ tailWord_2598859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598859).length < 2 ^ (prefixWord ++ tailWord_2598859).sum := by decide
  have hdescent : baseEnd_2598859 < baseStart_2598859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598879 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 6]
def baseStart_2598879 : Nat := 118140960795 + 2598879 * 2 ^ 59
def prefixEnd_2598879 : Nat := 4983230072969 + 3 ^ 40 * 2598879 * 2
def baseEnd_2598879 : Nat := 148274898875138067517831

theorem tailTrace_2598879 : CollatzResearch.WordTrace tailWord_2598879 prefixEnd_2598879 148274898875138067517831 := by
  unfold tailWord_2598879
  simp only [CollatzResearch.WordTrace]
  refine ⟨94788904351712711041351691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63192602901141807360901127 94788904351712711041351691)
  ·
    refine ⟨142183356527569066562027537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94788904351712711041351691 142183356527569066562027537)
    ·
      refine ⟨106637517395676799921520653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142183356527569066562027537 106637517395676799921520653)
      ·
        refine ⟨39989069023378799970570245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106637517395676799921520653 39989069023378799970570245)
        ·
          refine ⟨7497950441883524994481921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39989069023378799970570245 7497950441883524994481921)
          ·
            refine ⟨5623462831412643745861441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7497950441883524994481921 5623462831412643745861441)
            ·
              refine ⟨4217597123559482809396081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5623462831412643745861441 4217597123559482809396081)
              ·
                refine ⟨3163197842669612107047061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217597123559482809396081 3163197842669612107047061)
                ·
                  refine ⟨148274898875138067517831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3163197842669612107047061 148274898875138067517831)
                  ·
                    rfl

theorem cell23_2598879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 6].length) (baseStart_2598879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598879 prefixEnd_2598879 := by exact prefixLift 2598879
  have htrace : WordTrace (prefixWord ++ tailWord_2598879) baseStart_2598879 baseEnd_2598879 := by
    simpa [prefixWord, tailWord_2598879, baseEnd_2598879] using wordTrace_append hprefix tailTrace_2598879
  have hstable : (prefixWord ++ tailWord_2598879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598879).length < 2 ^ (prefixWord ++ tailWord_2598879).sum := by decide
  have hdescent : baseEnd_2598879 < baseStart_2598879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598883 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 1, 4]
def baseStart_2598883 : Nat := 118140960795 + 2598883 * 2 ^ 59
def prefixEnd_2598883 : Nat := 4983230072969 + 3 ^ 40 * 2598883 * 2
def baseEnd_2598883 : Nat := 444825381266286864003487

theorem tailTrace_2598883 : CollatzResearch.WordTrace tailWord_2598883 prefixEnd_2598883 444825381266286864003487 := by
  unfold tailWord_2598883
  simp only [CollatzResearch.WordTrace]
  refine ⟨94789050243698219724497303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63192700162465479816331535 94789050243698219724497303)
  ·
    refine ⟨142183575365547329586745955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94789050243698219724497303 142183575365547329586745955)
    ·
      refine ⟨213275363048320994380118933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142183575365547329586745955 213275363048320994380118933)
      ·
        refine ⟨9997282642890046611568075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213275363048320994380118933 9997282642890046611568075)
        ·
          refine ⟨14995923964335069917352113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9997282642890046611568075 14995923964335069917352113)
          ·
            refine ⟨11246942973251302438014085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14995923964335069917352113 11246942973251302438014085)
            ·
              refine ⟨2108801807484619207127641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11246942973251302438014085 2108801807484619207127641)
              ·
                refine ⟨1581601355613464405345731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108801807484619207127641 1581601355613464405345731)
                ·
                  refine ⟨2372402033420196608018597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581601355613464405345731 2372402033420196608018597)
                  ·
                    refine ⟨444825381266286864003487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372402033420196608018597 444825381266286864003487)
                    ·
                      rfl

theorem cell23_2598883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 4].length) (baseStart_2598883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598883 prefixEnd_2598883 := by exact prefixLift 2598883
  have htrace : WordTrace (prefixWord ++ tailWord_2598883) baseStart_2598883 baseEnd_2598883 := by
    simpa [prefixWord, tailWord_2598883, baseEnd_2598883] using wordTrace_append hprefix tailTrace_2598883
  have hstable : (prefixWord ++ tailWord_2598883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598883).length < 2 ^ (prefixWord ++ tailWord_2598883).sum := by decide
  have hdescent : baseEnd_2598883 < baseStart_2598883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598899 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 4, 3, 2]
def baseStart_2598899 : Nat := 118140960795 + 2598899 * 2 ^ 59
def prefixEnd_2598899 : Nat := 4983230072969 + 3 ^ 40 * 2598899 * 2
def baseEnd_2598899 : Nat := 1334484359489332529410387

theorem tailTrace_2598899 : CollatzResearch.WordTrace tailWord_2598899 prefixEnd_2598899 1334484359489332529410387 := by
  unfold tailWord_2598899
  simp only [CollatzResearch.WordTrace]
  refine ⟨94789633811640254457079751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63193089207760169638053167 94789633811640254457079751)
  ·
    refine ⟨142184450717460381685619627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94789633811640254457079751 142184450717460381685619627)
    ·
      refine ⟨213276676076190572528429441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142184450717460381685619627 213276676076190572528429441)
      ·
        refine ⟨159957507057142929396322081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213276676076190572528429441 159957507057142929396322081)
        ·
          refine ⟨119968130292857197047241561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159957507057142929396322081 119968130292857197047241561)
          ·
            refine ⟨89976097719642897785431171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119968130292857197047241561 89976097719642897785431171)
            ·
              refine ⟨134964146579464346678146757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89976097719642897785431171 134964146579464346678146757)
              ·
                refine ⟨25305777483649565002152517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134964146579464346678146757 25305777483649565002152517)
                ·
                  refine ⟨4744833278184293437903597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25305777483649565002152517 4744833278184293437903597)
                  ·
                    refine ⟨1779312479319110039213849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4744833278184293437903597 1779312479319110039213849)
                    ·
                      refine ⟨1334484359489332529410387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779312479319110039213849 1334484359489332529410387)
                      ·
                        rfl

theorem cell23_2598899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3, 2].length) (baseStart_2598899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598899 prefixEnd_2598899 := by exact prefixLift 2598899
  have htrace : WordTrace (prefixWord ++ tailWord_2598899) baseStart_2598899 baseEnd_2598899 := by
    simpa [prefixWord, tailWord_2598899, baseEnd_2598899] using wordTrace_append hprefix tailTrace_2598899
  have hstable : (prefixWord ++ tailWord_2598899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598899).length < 2 ^ (prefixWord ++ tailWord_2598899).sum := by decide
  have hdescent : baseEnd_2598899 < baseStart_2598899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598923 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 1, 1, 3]
def baseStart_2598923 : Nat := 118140960795 + 2598923 * 2 ^ 59
def prefixEnd_2598923 : Nat := 4983230072969 + 3 ^ 40 * 2598923 * 2
def baseEnd_2598923 : Nat := 1334496683025040435510277

theorem tailTrace_2598923 : CollatzResearch.WordTrace tailWord_2598923 prefixEnd_2598923 1334496683025040435510277 := by
  unfold tailWord_2598923
  simp only [CollatzResearch.WordTrace]
  refine ⟨94790509163553306555953423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63193672775702204370635615 94790509163553306555953423)
  ·
    refine ⟨142185763745329959833930135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94790509163553306555953423 142185763745329959833930135)
    ·
      refine ⟨213278645617994939750895203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142185763745329959833930135 213278645617994939750895203)
      ·
        refine ⟨319917968426992409626342805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213278645617994939750895203 319917968426992409626342805)
        ·
          refine ⟨14996154770015269201234819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 319917968426992409626342805 14996154770015269201234819)
          ·
            refine ⟨22494232155022903801852229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14996154770015269201234819 22494232155022903801852229)
            ·
              refine ⟨4217668529066794462847293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22494232155022903801852229 4217668529066794462847293)
              ·
                refine ⟨1581625698400047923567735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4217668529066794462847293 1581625698400047923567735)
                ·
                  refine ⟨2372438547600071885351603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581625698400047923567735 2372438547600071885351603)
                  ·
                    refine ⟨3558657821400107828027405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2372438547600071885351603 3558657821400107828027405)
                    ·
                      refine ⟨1334496683025040435510277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558657821400107828027405 1334496683025040435510277)
                      ·
                        rfl

theorem cell23_2598923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 1, 3].length) (baseStart_2598923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598923 prefixEnd_2598923 := by exact prefixLift 2598923
  have htrace : WordTrace (prefixWord ++ tailWord_2598923) baseStart_2598923 baseEnd_2598923 := by
    simpa [prefixWord, tailWord_2598923, baseEnd_2598923] using wordTrace_append hprefix tailTrace_2598923
  have hstable : (prefixWord ++ tailWord_2598923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598923).length < 2 ^ (prefixWord ++ tailWord_2598923).sum := by decide
  have hdescent : baseEnd_2598923 < baseStart_2598923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598939 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 2, 4]
def baseStart_2598939 : Nat := 118140960795 + 2598939 * 2 ^ 59
def prefixEnd_2598939 : Nat := 4983230072969 + 3 ^ 40 * 2598939 * 2
def baseEnd_2598939 : Nat := 444834966238504124303401

theorem tailTrace_2598939 : CollatzResearch.WordTrace tailWord_2598939 prefixEnd_2598939 444834966238504124303401 := by
  unfold tailWord_2598939
  simp only [CollatzResearch.WordTrace]
  refine ⟨94791092731495341288535871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63194061820996894192357247 94791092731495341288535871)
  ·
    refine ⟨142186639097243011932803807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94791092731495341288535871 142186639097243011932803807)
    ·
      refine ⟨213279958645864517899205711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142186639097243011932803807 213279958645864517899205711)
      ·
        refine ⟨319919937968796776848808567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213279958645864517899205711 319919937968796776848808567)
        ·
          refine ⟨479879906953195165273212851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319919937968796776848808567 479879906953195165273212851)
          ·
            refine ⟨719819860429792747909819277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479879906953195165273212851 719819860429792747909819277)
            ·
              refine ⟨269932447661172280466182229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 719819860429792747909819277 269932447661172280466182229)
              ·
                refine ⟨3163270871029362661713073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 269932447661172280466182229 3163270871029362661713073)
                ·
                  refine ⟨2372453153272021996284805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163270871029362661713073 2372453153272021996284805)
                  ·
                    refine ⟨444834966238504124303401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372453153272021996284805 444834966238504124303401)
                    ·
                      rfl

theorem cell23_2598939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 4].length) (baseStart_2598939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598939 prefixEnd_2598939 := by exact prefixLift 2598939
  have htrace : WordTrace (prefixWord ++ tailWord_2598939) baseStart_2598939 baseEnd_2598939 := by
    simpa [prefixWord, tailWord_2598939, baseEnd_2598939] using wordTrace_append hprefix tailTrace_2598939
  have hstable : (prefixWord ++ tailWord_2598939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598939).length < 2 ^ (prefixWord ++ tailWord_2598939).sum := by decide
  have hdescent : baseEnd_2598939 < baseStart_2598939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598949 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_2598949 : Nat := 118140960795 + 2598949 * 2 ^ 59
def prefixEnd_2598949 : Nat := 4983230072969 + 3 ^ 40 * 2598949 * 2
def baseEnd_2598949 : Nat := 1334510033522057333785157

theorem tailTrace_2598949 : CollatzResearch.WordTrace tailWord_2598949 prefixEnd_2598949 1334510033522057333785157 := by
  unfold tailWord_2598949
  simp only [CollatzResearch.WordTrace]
  refine ⟨94791457461459112996399901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63194304974306075330933267 94791457461459112996399901)
  ·
    refine ⟨35546796548047167373649963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94791457461459112996399901 35546796548047167373649963)
    ·
      refine ⟨53320194822070751060474945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35546796548047167373649963 53320194822070751060474945)
      ·
        refine ⟨39990146116553063295356209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53320194822070751060474945 39990146116553063295356209)
        ·
          refine ⟨29992609587414797471517157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39990146116553063295356209 29992609587414797471517157)
          ·
            refine ⟨5623614297640274525909467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29992609587414797471517157 5623614297640274525909467)
            ·
              refine ⟨8435421446460411788864201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623614297640274525909467 8435421446460411788864201)
              ·
                refine ⟨6326566084845308841648151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8435421446460411788864201 6326566084845308841648151)
                ·
                  refine ⟨9489849127267963262472227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6326566084845308841648151 9489849127267963262472227)
                  ·
                    refine ⟨14234773690901944893708341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9489849127267963262472227 14234773690901944893708341)
                    ·
                      refine ⟨1334510033522057333785157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14234773690901944893708341 1334510033522057333785157)
                      ·
                        rfl

theorem cell23_2598949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_2598949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598949 prefixEnd_2598949 := by exact prefixLift 2598949
  have htrace : WordTrace (prefixWord ++ tailWord_2598949) baseStart_2598949 baseEnd_2598949 := by
    simpa [prefixWord, tailWord_2598949, baseEnd_2598949] using wordTrace_append hprefix tailTrace_2598949
  have hstable : (prefixWord ++ tailWord_2598949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598949).length < 2 ^ (prefixWord ++ tailWord_2598949).sum := by decide
  have hdescent : baseEnd_2598949 < baseStart_2598949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598969 : List Nat := [1, 2, 1, 5, 3, 1, 1, 9]
def baseStart_2598969 : Nat := 118140960795 + 2598969 * 2 ^ 59
def prefixEnd_2598969 : Nat := 4983230072969 + 3 ^ 40 * 2598969 * 2
def baseEnd_2598969 : Nat := 49426677893894342797595

theorem tailTrace_2598969 : CollatzResearch.WordTrace tailWord_2598969 prefixEnd_2598969 49426677893894342797595 := by
  unfold tailWord_2598969
  simp only [CollatzResearch.WordTrace]
  refine ⟨94792186921386656412127961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63194791280924437608085307 94792186921386656412127961)
  ·
    refine ⟨71094140191039992309095971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94792186921386656412127961 71094140191039992309095971)
    ·
      refine ⟨106641210286559988463643957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71094140191039992309095971 106641210286559988463643957)
      ·
        refine ⟨9997613464364998918466621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106641210286559988463643957 9997613464364998918466621)
        ·
          refine ⟨3749105049136874594424983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9997613464364998918466621 3749105049136874594424983)
          ·
            refine ⟨5623657573705311891637475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749105049136874594424983 5623657573705311891637475)
            ·
              refine ⟨8435486360557967837456213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623657573705311891637475 8435486360557967837456213)
              ·
                refine ⟨49426677893894342797595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8435486360557967837456213 49426677893894342797595)
                ·
                  rfl

theorem cell23_2598969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 9].length) (baseStart_2598969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598969 prefixEnd_2598969 := by exact prefixLift 2598969
  have htrace : WordTrace (prefixWord ++ tailWord_2598969) baseStart_2598969 baseEnd_2598969 := by
    simpa [prefixWord, tailWord_2598969, baseEnd_2598969] using wordTrace_append hprefix tailTrace_2598969
  have hstable : (prefixWord ++ tailWord_2598969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598969).length < 2 ^ (prefixWord ++ tailWord_2598969).sum := by decide
  have hdescent : baseEnd_2598969 < baseStart_2598969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598974 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2598974 : Nat := 118140960795 + 2598974 * 2 ^ 59
def prefixEnd_2598974 : Nat := 4983230072969 + 3 ^ 40 * 2598974 * 2
def baseEnd_2598974 : Nat := 1334522870538419735972543

theorem tailTrace_2598974 : CollatzResearch.WordTrace tailWord_2598974 prefixEnd_2598974 1334522870538419735972543 := by
  unfold tailWord_2598974
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849046160796067783257497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63194912857579028177373317 11849046160796067783257497)
  ·
    refine ⟨8886784620597050837443123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11849046160796067783257497 8886784620597050837443123)
    ·
      refine ⟨13330176930895576256164685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886784620597050837443123 13330176930895576256164685)
      ·
        refine ⟨4998816349085841096061757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13330176930895576256164685 4998816349085841096061757)
        ·
          refine ⟨1874556130907190411023159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4998816349085841096061757 1874556130907190411023159)
          ·
            refine ⟨2811834196360785616534739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874556130907190411023159 2811834196360785616534739)
            ·
              refine ⟨4217751294541178424802109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811834196360785616534739 4217751294541178424802109)
              ·
                refine ⟨1581656735452941909300791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4217751294541178424802109 1581656735452941909300791)
                ·
                  refine ⟨2372485103179412863951187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581656735452941909300791 2372485103179412863951187)
                  ·
                    refine ⟨3558727654769119295926781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2372485103179412863951187 3558727654769119295926781)
                    ·
                      refine ⟨1334522870538419735972543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558727654769119295926781 1334522870538419735972543)
                      ·
                        rfl

theorem cell23_2598974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2598974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598974 prefixEnd_2598974 := by exact prefixLift 2598974
  have htrace : WordTrace (prefixWord ++ tailWord_2598974) baseStart_2598974 baseEnd_2598974 := by
    simpa [prefixWord, tailWord_2598974, baseEnd_2598974] using wordTrace_append hprefix tailTrace_2598974
  have hstable : (prefixWord ++ tailWord_2598974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598974).length < 2 ^ (prefixWord ++ tailWord_2598974).sum := by decide
  have hdescent : baseEnd_2598974 < baseStart_2598974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598997 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_2598997 : Nat := 118140960795 + 2598997 * 2 ^ 59
def prefixEnd_2598997 : Nat := 4983230072969 + 3 ^ 40 * 2598997 * 2
def baseEnd_2598997 : Nat := 1334534680593473145984937

theorem tailTrace_2598997 : CollatzResearch.WordTrace tailWord_2598997 prefixEnd_2598997 1334534680593473145984937 := by
  unfold tailWord_2598997
  simp only [CollatzResearch.WordTrace]
  refine ⟨94793208165285217194147245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63195472110190144796098163 94793208165285217194147245)
  ·
    refine ⟨35547453061981956447805217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94793208165285217194147245 35547453061981956447805217)
    ·
      refine ⟨26660589796486467335853913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35547453061981956447805217 26660589796486467335853913)
      ·
        refine ⟨19995442347364850501890435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26660589796486467335853913 19995442347364850501890435)
        ·
          refine ⟨29993163521047275752835653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19995442347364850501890435 29993163521047275752835653)
          ·
            refine ⟨5623718160196364203656685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29993163521047275752835653 5623718160196364203656685)
            ·
              refine ⟨2108894310073636576371257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5623718160196364203656685 2108894310073636576371257)
              ·
                refine ⟨1581670732555227432278443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108894310073636576371257 1581670732555227432278443)
                ·
                  refine ⟨2372506098832841148417665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581670732555227432278443 2372506098832841148417665)
                  ·
                    refine ⟨1779379574124630861313249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2372506098832841148417665 1779379574124630861313249)
                    ·
                      refine ⟨1334534680593473145984937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779379574124630861313249 1334534680593473145984937)
                      ·
                        rfl

theorem cell23_2598997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_2598997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2598997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2598997 prefixEnd_2598997 := by exact prefixLift 2598997
  have htrace : WordTrace (prefixWord ++ tailWord_2598997) baseStart_2598997 baseEnd_2598997 := by
    simpa [prefixWord, tailWord_2598997, baseEnd_2598997] using wordTrace_append hprefix tailTrace_2598997
  have hstable : (prefixWord ++ tailWord_2598997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598997).length < 2 ^ (prefixWord ++ tailWord_2598997).sum := by decide
  have hdescent : baseEnd_2598997 < baseStart_2598997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599013 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_2599013 : Nat := 118140960795 + 2599013 * 2 ^ 59
def prefixEnd_2599013 : Nat := 4983230072969 + 3 ^ 40 * 2599013 * 2
def baseEnd_2599013 : Nat := 1334542896283945083384863

theorem tailTrace_2599013 : CollatzResearch.WordTrace tailWord_2599013 prefixEnd_2599013 1334542896283945083384863 := by
  unfold tailWord_2599013
  simp only [CollatzResearch.WordTrace]
  refine ⟨94793791733227251926729693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63195861155484834617819795 94793791733227251926729693)
  ·
    refine ⟨35547671899960219472523635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94793791733227251926729693 35547671899960219472523635)
    ·
      refine ⟨53321507849940329208785453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35547671899960219472523635 53321507849940329208785453)
      ·
        refine ⟨19995565443727623453294545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53321507849940329208785453 19995565443727623453294545)
        ·
          refine ⟨14996674082795717589970909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19995565443727623453294545 14996674082795717589970909)
          ·
            refine ⟨5623752781048394096239091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14996674082795717589970909 5623752781048394096239091)
            ·
              refine ⟨8435629171572591144358637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623752781048394096239091 8435629171572591144358637)
              ·
                refine ⟨3163360939339721679134489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8435629171572591144358637 3163360939339721679134489)
                ·
                  refine ⟨2372520704504791259350867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163360939339721679134489 2372520704504791259350867)
                  ·
                    refine ⟨3558781056757186889026301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2372520704504791259350867 3558781056757186889026301)
                    ·
                      refine ⟨1334542896283945083384863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558781056757186889026301 1334542896283945083384863)
                      ·
                        rfl

theorem cell23_2599013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_2599013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599013 prefixEnd_2599013 := by exact prefixLift 2599013
  have htrace : WordTrace (prefixWord ++ tailWord_2599013) baseStart_2599013 baseEnd_2599013 := by
    simpa [prefixWord, tailWord_2599013, baseEnd_2599013] using wordTrace_append hprefix tailTrace_2599013
  have hstable : (prefixWord ++ tailWord_2599013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599013).length < 2 ^ (prefixWord ++ tailWord_2599013).sum := by decide
  have hdescent : baseEnd_2599013 < baseStart_2599013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599023 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 1, 3, 2]
def baseStart_2599023 : Nat := 118140960795 + 2599023 * 2 ^ 59
def prefixEnd_2599023 : Nat := 4983230072969 + 3 ^ 40 * 2599023 * 2
def baseEnd_2599023 : Nat := 1334548031090490044259817

theorem tailTrace_2599023 : CollatzResearch.WordTrace tailWord_2599023 prefixEnd_2599023 1334548031090490044259817 := by
  unfold tailWord_2599023
  simp only [CollatzResearch.WordTrace]
  refine ⟨94794156463191023634593723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63196104308794015756395815 94794156463191023634593723)
  ·
    refine ⟨142191234694786535451890585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94794156463191023634593723 142191234694786535451890585)
    ·
      refine ⟨106643426021089901588917939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142191234694786535451890585 106643426021089901588917939)
      ·
        refine ⟨159965139031634852383376909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106643426021089901588917939 159965139031634852383376909)
        ·
          refine ⟨59986927136863069643766341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159965139031634852383376909 59986927136863069643766341)
          ·
            refine ⟨11247548838161825558206189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59986927136863069643766341 11247548838161825558206189)
            ·
              refine ⟨4217830814310684584327321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11247548838161825558206189 4217830814310684584327321)
              ·
                refine ⟨3163373110733013438245491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217830814310684584327321 3163373110733013438245491)
                ·
                  refine ⟨4745059666099520157368237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163373110733013438245491 4745059666099520157368237)
                  ·
                    refine ⟨1779397374787320059013089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4745059666099520157368237 1779397374787320059013089)
                    ·
                      refine ⟨1334548031090490044259817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779397374787320059013089 1334548031090490044259817)
                      ·
                        rfl

theorem cell23_2599023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 3, 2].length) (baseStart_2599023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599023 prefixEnd_2599023 := by exact prefixLift 2599023
  have htrace : WordTrace (prefixWord ++ tailWord_2599023) baseStart_2599023 baseEnd_2599023 := by
    simpa [prefixWord, tailWord_2599023, baseEnd_2599023] using wordTrace_append hprefix tailTrace_2599023
  have hstable : (prefixWord ++ tailWord_2599023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599023).length < 2 ^ (prefixWord ++ tailWord_2599023).sum := by decide
  have hdescent : baseEnd_2599023 < baseStart_2599023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599036 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_2599036 : Nat := 118140960795 + 2599036 * 2 ^ 59
def prefixEnd_2599036 : Nat := 4983230072969 + 3 ^ 40 * 2599036 * 2
def baseEnd_2599036 : Nat := 1334554706338998493397257

theorem tailTrace_2599036 : CollatzResearch.WordTrace tailWord_2599036 prefixEnd_2599036 1334554706338998493397257 := by
  unfold tailWord_2599036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47397315306071963427408481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63196420408095951236544641 47397315306071963427408481)
  ·
    refine ⟨35547986479553972570556361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47397315306071963427408481 35547986479553972570556361)
    ·
      refine ⟨26660989859665479427917271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35547986479553972570556361 26660989859665479427917271)
      ·
        refine ⟨39991484789498219141875907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26660989859665479427917271 39991484789498219141875907)
        ·
          refine ⟨59987227184247328712813861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39991484789498219141875907 59987227184247328712813861)
          ·
            refine ⟨11247605097046374133652599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59987227184247328712813861 11247605097046374133652599)
            ·
              refine ⟨16871407645569561200478899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11247605097046374133652599 16871407645569561200478899)
              ·
                refine ⟨25307111468354341800718349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16871407645569561200478899 25307111468354341800718349)
                ·
                  refine ⟨9490166800632878175269381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25307111468354341800718349 9490166800632878175269381)
                  ·
                    refine ⟨1779406275118664657863009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9490166800632878175269381 1779406275118664657863009)
                    ·
                      refine ⟨1334554706338998493397257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779406275118664657863009 1334554706338998493397257)
                      ·
                        rfl

theorem cell23_2599036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_2599036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599036 prefixEnd_2599036 := by exact prefixLift 2599036
  have htrace : WordTrace (prefixWord ++ tailWord_2599036) baseStart_2599036 baseEnd_2599036 := by
    simpa [prefixWord, tailWord_2599036, baseEnd_2599036] using wordTrace_append hprefix tailTrace_2599036
  have hstable : (prefixWord ++ tailWord_2599036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599036).length < 2 ^ (prefixWord ++ tailWord_2599036).sum := by decide
  have hdescent : baseEnd_2599036 < baseStart_2599036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599049 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_2599049 : Nat := 118140960795 + 2599049 * 2 ^ 59
def prefixEnd_2599049 : Nat := 4983230072969 + 3 ^ 40 * 2599049 * 2
def baseEnd_2599049 : Nat := 1334561381587506942534697

theorem tailTrace_2599049 : CollatzResearch.WordTrace tailWord_2599049 prefixEnd_2599049 1334561381587506942534697 := by
  unfold tailWord_2599049
  simp only [CollatzResearch.WordTrace]
  refine ⟨94795104761096830075040201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63196736507397886716693467 94795104761096830075040201)
  ·
    refine ⟨71096328570822622556280151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94795104761096830075040201 71096328570822622556280151)
    ·
      refine ⟨106644492856233933834420227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71096328570822622556280151 106644492856233933834420227)
      ·
        refine ⟨159966739284350900751630341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106644492856233933834420227 159966739284350900751630341)
        ·
          refine ⟨29993763615815793890930689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159966739284350900751630341 29993763615815793890930689)
          ·
            refine ⟨22495322711861845418198017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29993763615815793890930689 22495322711861845418198017)
            ·
              refine ⟨16871492033896384063648513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22495322711861845418198017 16871492033896384063648513)
              ·
                refine ⟨12653619025422288047736385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16871492033896384063648513 12653619025422288047736385)
                ·
                  refine ⟨9490214269066716035802289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12653619025422288047736385 9490214269066716035802289)
                  ·
                    refine ⟨7117660701800037026851717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9490214269066716035802289 7117660701800037026851717)
                    ·
                      refine ⟨1334561381587506942534697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7117660701800037026851717 1334561381587506942534697)
                      ·
                        rfl

theorem cell23_2599049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_2599049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599049 prefixEnd_2599049 := by exact prefixLift 2599049
  have htrace : WordTrace (prefixWord ++ tailWord_2599049) baseStart_2599049 baseEnd_2599049 := by
    simpa [prefixWord, tailWord_2599049, baseEnd_2599049] using wordTrace_append hprefix tailTrace_2599049
  have hstable : (prefixWord ++ tailWord_2599049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599049).length < 2 ^ (prefixWord ++ tailWord_2599049).sum := by decide
  have hdescent : baseEnd_2599049 < baseStart_2599049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599076 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 7]
def baseStart_2599076 : Nat := 118140960795 + 2599076 * 2 ^ 59
def prefixEnd_2599076 : Nat := 4983230072969 + 3 ^ 40 * 2599076 * 2
def baseEnd_2599076 : Nat := 148286138396130926321897

theorem tailTrace_2599076 : CollatzResearch.WordTrace tailWord_2599076 prefixEnd_2599076 148286138396130926321897 := by
  unfold tailWord_2599076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47398044765999506843136541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63197393021332675790848721 47398044765999506843136541)
  ·
    refine ⟨17774266787249815066176203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47398044765999506843136541 17774266787249815066176203)
    ·
      refine ⟨26661400180874722599264305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17774266787249815066176203 26661400180874722599264305)
      ·
        refine ⟨19996050135656041949448229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26661400180874722599264305 19996050135656041949448229)
        ·
          refine ⟨3749259400435507865521543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19996050135656041949448229 3749259400435507865521543)
          ·
            refine ⟨5623889100653261798282315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749259400435507865521543 5623889100653261798282315)
            ·
              refine ⟨8435833650979892697423473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623889100653261798282315 8435833650979892697423473)
              ·
                refine ⟨6326875238234919523067605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8435833650979892697423473 6326875238234919523067605)
                ·
                  refine ⟨148286138396130926321897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6326875238234919523067605 148286138396130926321897)
                  ·
                    rfl

theorem cell23_2599076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_2599076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599076 prefixEnd_2599076 := by exact prefixLift 2599076
  have htrace : WordTrace (prefixWord ++ tailWord_2599076) baseStart_2599076 baseEnd_2599076 := by
    simpa [prefixWord, tailWord_2599076, baseEnd_2599076] using wordTrace_append hprefix tailTrace_2599076
  have hstable : (prefixWord ++ tailWord_2599076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599076).length < 2 ^ (prefixWord ++ tailWord_2599076).sum := by decide
  have hdescent : baseEnd_2599076 < baseStart_2599076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599136 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 3, 4]
def baseStart_2599136 : Nat := 118140960795 + 2599136 * 2 ^ 59
def prefixEnd_2599136 : Nat := 4983230072969 + 3 ^ 40 * 2599136 * 2
def baseEnd_2599136 : Nat := 444868684801482700715599

theorem tailTrace_2599136 : CollatzResearch.WordTrace tailWord_2599136 prefixEnd_2599136 444868684801482700715599 := by
  unfold tailWord_2599136
  simp only [CollatzResearch.WordTrace]
  refine ⟨47399138955890821966728631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63198851941187762622304841 47399138955890821966728631)
  ·
    refine ⟨71098708433836232950092947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47399138955890821966728631 71098708433836232950092947)
    ·
      refine ⟨106648062650754349425139421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71098708433836232950092947 106648062650754349425139421)
      ·
        refine ⟨39993023494032881034427283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106648062650754349425139421 39993023494032881034427283)
        ·
          refine ⟨59989535241049321551640925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39993023494032881034427283 59989535241049321551640925)
          ·
            refine ⟨22496075715393495581865347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59989535241049321551640925 22496075715393495581865347)
            ·
              refine ⟨33744113573090243372798021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22496075715393495581865347 33744113573090243372798021)
              ·
                refine ⟨6327021294954420632399629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33744113573090243372798021 6327021294954420632399629)
                ·
                  refine ⟨2372632985607907737149861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6327021294954420632399629 2372632985607907737149861)
                  ·
                    refine ⟨444868684801482700715599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372632985607907737149861 444868684801482700715599)
                    ·
                      rfl

theorem cell23_2599136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_2599136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599136 prefixEnd_2599136 := by exact prefixLift 2599136
  have htrace : WordTrace (prefixWord ++ tailWord_2599136) baseStart_2599136 baseEnd_2599136 := by
    simpa [prefixWord, tailWord_2599136, baseEnd_2599136] using wordTrace_append hprefix tailTrace_2599136
  have hstable : (prefixWord ++ tailWord_2599136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599136).length < 2 ^ (prefixWord ++ tailWord_2599136).sum := by decide
  have hdescent : baseEnd_2599136 < baseStart_2599136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599146 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_2599146 : Nat := 118140960795 + 2599146 * 2 ^ 59
def prefixEnd_2599146 : Nat := 4983230072969 + 3 ^ 40 * 2599146 * 2
def baseEnd_2599146 : Nat := 1334611189210993063021751

theorem tailTrace_2599146 : CollatzResearch.WordTrace tailWord_2599146 prefixEnd_2599146 1334611189210993063021751 := by
  unfold tailWord_2599146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23699660660436353910330323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63199095094496943760880861 23699660660436353910330323)
  ·
    refine ⟨35549490990654530865495485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23699660660436353910330323 35549490990654530865495485)
    ·
      refine ⟨13331059121495449074560807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35549490990654530865495485 13331059121495449074560807)
      ·
        refine ⟨19996588682243173611841211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331059121495449074560807 19996588682243173611841211)
        ·
          refine ⟨29994883023364760417761817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19996588682243173611841211 29994883023364760417761817)
          ·
            refine ⟨22496162267523570313321363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29994883023364760417761817 22496162267523570313321363)
            ·
              refine ⟨33744243401285355469982045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22496162267523570313321363 33744243401285355469982045)
              ·
                refine ⟨12654091275482008301243267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33744243401285355469982045 12654091275482008301243267)
                ·
                  refine ⟨18981136913223012451864901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12654091275482008301243267 18981136913223012451864901)
                  ·
                    refine ⟨3558963171229314834724669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18981136913223012451864901 3558963171229314834724669)
                    ·
                      refine ⟨1334611189210993063021751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3558963171229314834724669 1334611189210993063021751)
                      ·
                        rfl

theorem cell23_2599146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_2599146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599146 prefixEnd_2599146 := by exact prefixLift 2599146
  have htrace : WordTrace (prefixWord ++ tailWord_2599146) baseStart_2599146 baseEnd_2599146 := by
    simpa [prefixWord, tailWord_2599146, baseEnd_2599146] using wordTrace_append hprefix tailTrace_2599146
  have hstable : (prefixWord ++ tailWord_2599146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599146).length < 2 ^ (prefixWord ++ tailWord_2599146).sum := by decide
  have hdescent : baseEnd_2599146 < baseStart_2599146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599166 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_2599166 : Nat := 118140960795 + 2599166 * 2 ^ 59
def prefixEnd_2599166 : Nat := 4983230072969 + 3 ^ 40 * 2599166 * 2
def baseEnd_2599166 : Nat := 148291273202675887196851

theorem tailTrace_2599166 : CollatzResearch.WordTrace tailWord_2599166 prefixEnd_2599166 148291273202675887196851 := by
  unfold tailWord_2599166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849921512709119882131169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63199581401115306038032901 11849921512709119882131169)
  ·
    refine ⟨8887441134531839911598377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11849921512709119882131169 8887441134531839911598377)
    ·
      refine ⟨6665580850898879933698783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8887441134531839911598377 6665580850898879933698783)
      ·
        refine ⟨9998371276348319900548175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665580850898879933698783 9998371276348319900548175)
        ·
          refine ⟨14997556914522479850822263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9998371276348319900548175 14997556914522479850822263)
          ·
            refine ⟨22496335371783719776233395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14997556914522479850822263 22496335371783719776233395)
            ·
              refine ⟨33744503057675579664350093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22496335371783719776233395 33744503057675579664350093)
              ·
                refine ⟨12654188646628342374131285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33744503057675579664350093 12654188646628342374131285)
                ·
                  refine ⟨148291273202675887196851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12654188646628342374131285 148291273202675887196851)
                  ·
                    rfl

theorem cell23_2599166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_2599166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599166 prefixEnd_2599166 := by exact prefixLift 2599166
  have htrace : WordTrace (prefixWord ++ tailWord_2599166) baseStart_2599166 baseEnd_2599166 := by
    simpa [prefixWord, tailWord_2599166, baseEnd_2599166] using wordTrace_append hprefix tailTrace_2599166
  have hstable : (prefixWord ++ tailWord_2599166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599166).length < 2 ^ (prefixWord ++ tailWord_2599166).sum := by decide
  have hdescent : baseEnd_2599166 < baseStart_2599166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599170 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2599170 : Nat := 118140960795 + 2599170 * 2 ^ 59
def prefixEnd_2599170 : Nat := 4983230072969 + 3 ^ 40 * 2599170 * 2
def baseEnd_2599170 : Nat := 444874504248900323040547

theorem tailTrace_2599170 : CollatzResearch.WordTrace tailWord_2599170 prefixEnd_2599170 444874504248900323040547 := by
  unfold tailWord_2599170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23699879498414616935048741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63199678662438978493463309 23699879498414616935048741)
  ·
    refine ⟨4443727405952740675321639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23699879498414616935048741 4443727405952740675321639)
    ·
      refine ⟨6665591108929111012982459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443727405952740675321639 6665591108929111012982459)
      ·
        refine ⟨9998386663393666519473689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665591108929111012982459 9998386663393666519473689)
        ·
          refine ⟨7498789997545249889605267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9998386663393666519473689 7498789997545249889605267)
          ·
            refine ⟨11248184996317874834407901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7498789997545249889605267 11248184996317874834407901)
            ·
              refine ⟨4218069373619203062902963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11248184996317874834407901 4218069373619203062902963)
              ·
                refine ⟨6327104060428804594354445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218069373619203062902963 6327104060428804594354445)
                ·
                  refine ⟨2372664022660801722882917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6327104060428804594354445 2372664022660801722882917)
                  ·
                    refine ⟨444874504248900323040547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372664022660801722882917 444874504248900323040547)
                    ·
                      rfl

theorem cell23_2599170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2599170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599170 prefixEnd_2599170 := by exact prefixLift 2599170
  have htrace : WordTrace (prefixWord ++ tailWord_2599170) baseStart_2599170 baseEnd_2599170 := by
    simpa [prefixWord, tailWord_2599170, baseEnd_2599170] using wordTrace_append hprefix tailTrace_2599170
  have hstable : (prefixWord ++ tailWord_2599170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599170).length < 2 ^ (prefixWord ++ tailWord_2599170).sum := by decide
  have hdescent : baseEnd_2599170 < baseStart_2599170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599250 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_2599250 : Nat := 118140960795 + 2599250 * 2 ^ 59
def prefixEnd_2599250 : Nat := 4983230072969 + 3 ^ 40 * 2599250 * 2
def baseEnd_2599250 : Nat := 1334664591199060656121273

theorem tailTrace_2599250 : CollatzResearch.WordTrace tailWord_2599250 prefixEnd_2599250 1334664591199060656121273 := by
  unfold tailWord_2599250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700608958342160350776801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63201623888912427602071469 23700608958342160350776801)
  ·
    refine ⟨17775456718756620263082601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23700608958342160350776801 17775456718756620263082601)
    ·
      refine ⟨13331592539067465197311951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17775456718756620263082601 13331592539067465197311951)
      ·
        refine ⟨19997388808601197795967927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331592539067465197311951 19997388808601197795967927)
        ·
          refine ⟨29996083212901796693951891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19997388808601197795967927 29996083212901796693951891)
          ·
            refine ⟨44994124819352695040927837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29996083212901796693951891 44994124819352695040927837)
            ·
              refine ⟨16872796807257260640347939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44994124819352695040927837 16872796807257260640347939)
              ·
                refine ⟨25309195210885890960521909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16872796807257260640347939 25309195210885890960521909)
                ·
                  refine ⟨2372737051020552277548929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25309195210885890960521909 2372737051020552277548929)
                  ·
                    refine ⟨1779552788265414208161697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2372737051020552277548929 1779552788265414208161697)
                    ·
                      refine ⟨1334664591199060656121273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779552788265414208161697 1334664591199060656121273)
                      ·
                        rfl

theorem cell23_2599250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_2599250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599250 prefixEnd_2599250 := by exact prefixLift 2599250
  have htrace : WordTrace (prefixWord ++ tailWord_2599250) baseStart_2599250 baseEnd_2599250 := by
    simpa [prefixWord, tailWord_2599250, baseEnd_2599250] using wordTrace_append hprefix tailTrace_2599250
  have hstable : (prefixWord ++ tailWord_2599250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599250).length < 2 ^ (prefixWord ++ tailWord_2599250).sum := by decide
  have hdescent : baseEnd_2599250 < baseStart_2599250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599283 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 3]
def baseStart_2599283 : Nat := 118140960795 + 2599283 * 2 ^ 59
def prefixEnd_2599283 : Nat := 4983230072969 + 3 ^ 40 * 2599283 * 2
def baseEnd_2599283 : Nat := 1334681536060659027008621

theorem tailTrace_2599283 : CollatzResearch.WordTrace tailWord_2599283 prefixEnd_2599283 1334681536060659027008621 := by
  unfold tailWord_2599283
  simp only [CollatzResearch.WordTrace]
  refine ⟨94803639442249088039058503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63202426294832725359372335 94803639442249088039058503)
  ·
    refine ⟨142205459163373632058587755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94803639442249088039058503 142205459163373632058587755)
    ·
      refine ⟨213308188745060448087881633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142205459163373632058587755 213308188745060448087881633)
      ·
        refine ⟨159981141558795336065911225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213308188745060448087881633 159981141558795336065911225)
        ·
          refine ⟨119985856169096502049433419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159981141558795336065911225 119985856169096502049433419)
          ·
            refine ⟨179978784253644753074150129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119985856169096502049433419 179978784253644753074150129)
            ·
              refine ⟨134984088190233564805612597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179978784253644753074150129 134984088190233564805612597)
              ·
                refine ⟨12654758267834396700526181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134984088190233564805612597 12654758267834396700526181)
                ·
                  refine ⟨2372767175218949381348659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12654758267834396700526181 2372767175218949381348659)
                  ·
                    refine ⟨3559150762828424072022989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2372767175218949381348659 3559150762828424072022989)
                    ·
                      refine ⟨1334681536060659027008621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3559150762828424072022989 1334681536060659027008621)
                      ·
                        rfl

theorem cell23_2599283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_2599283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599283 prefixEnd_2599283 := by exact prefixLift 2599283
  have htrace : WordTrace (prefixWord ++ tailWord_2599283) baseStart_2599283 baseEnd_2599283 := by
    simpa [prefixWord, tailWord_2599283, baseEnd_2599283] using wordTrace_append hprefix tailTrace_2599283
  have hstable : (prefixWord ++ tailWord_2599283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599283).length < 2 ^ (prefixWord ++ tailWord_2599283).sum := by decide
  have hdescent : baseEnd_2599283 < baseStart_2599283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599361 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2599361 : Nat := 118140960795 + 2599361 * 2 ^ 59
def prefixEnd_2599361 : Nat := 4983230072969 + 3 ^ 40 * 2599361 * 2
def baseEnd_2599361 : Nat := 1334721587551709721833263

theorem tailTrace_2599361 : CollatzResearch.WordTrace tailWord_2599361 prefixEnd_2599361 1334721587551709721833263 := by
  unfold tailWord_2599361
  simp only [CollatzResearch.WordTrace]
  refine ⟨94806484335966507360397937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63204322890644338240265291 94806484335966507360397937)
  ·
    refine ⟨71104863251974880520298453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94806484335966507360397937 71104863251974880520298453)
    ·
      refine ⟨1666520232468161262194495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 71104863251974880520298453 1666520232468161262194495)
      ·
        refine ⟨2499780348702241893291743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666520232468161262194495 2499780348702241893291743)
        ·
          refine ⟨3749670523053362839937615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499780348702241893291743 3749670523053362839937615)
          ·
            refine ⟨5624505784580044259906423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749670523053362839937615 5624505784580044259906423)
            ·
              refine ⟨8436758676870066389859635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624505784580044259906423 8436758676870066389859635)
              ·
                refine ⟨12655138015305099584789453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8436758676870066389859635 12655138015305099584789453)
                ·
                  refine ⟨4745676755739412344296045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12655138015305099584789453 4745676755739412344296045)
                  ·
                    refine ⟨1779628783402279629111017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4745676755739412344296045 1779628783402279629111017)
                    ·
                      refine ⟨1334721587551709721833263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779628783402279629111017 1334721587551709721833263)
                      ·
                        rfl

theorem cell23_2599361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2599361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599361 prefixEnd_2599361 := by exact prefixLift 2599361
  have htrace : WordTrace (prefixWord ++ tailWord_2599361) baseStart_2599361 baseEnd_2599361 := by
    simpa [prefixWord, tailWord_2599361, baseEnd_2599361] using wordTrace_append hprefix tailTrace_2599361
  have hstable : (prefixWord ++ tailWord_2599361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599361).length < 2 ^ (prefixWord ++ tailWord_2599361).sum := by decide
  have hdescent : baseEnd_2599361 < baseStart_2599361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599393 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2599393 : Nat := 118140960795 + 2599393 * 2 ^ 59
def prefixEnd_2599393 : Nat := 4983230072969 + 3 ^ 40 * 2599393 * 2
def baseEnd_2599393 : Nat := 444912672977551198877705

theorem tailTrace_2599393 : CollatzResearch.WordTrace tailWord_2599393 prefixEnd_2599393 444912672977551198877705 := by
  unfold tailWord_2599393
  simp only [CollatzResearch.WordTrace]
  refine ⟨94807651471850576825562833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63205100981233717883708555 94807651471850576825562833)
  ·
    refine ⟨71105738603887932619172125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94807651471850576825562833 71105738603887932619172125)
    ·
      refine ⟨26664651976457974732189547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71105738603887932619172125 26664651976457974732189547)
      ·
        refine ⟨39996977964686962098284321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26664651976457974732189547 39996977964686962098284321)
        ·
          refine ⟨29997733473515221573713241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39996977964686962098284321 29997733473515221573713241)
          ·
            refine ⟨22498300105136416180284931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29997733473515221573713241 22498300105136416180284931)
            ·
              refine ⟨33747450157704624270427397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22498300105136416180284931 33747450157704624270427397)
              ·
                refine ⟨6327646904569617050705137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33747450157704624270427397 6327646904569617050705137)
                ·
                  refine ⟨4745735178427212788028853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327646904569617050705137 4745735178427212788028853)
                  ·
                    refine ⟨444912672977551198877705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4745735178427212788028853 444912672977551198877705)
                    ·
                      rfl

theorem cell23_2599393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2599393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599393 prefixEnd_2599393 := by exact prefixLift 2599393
  have htrace : WordTrace (prefixWord ++ tailWord_2599393) baseStart_2599393 baseEnd_2599393 := by
    simpa [prefixWord, tailWord_2599393, baseEnd_2599393] using wordTrace_append hprefix tailTrace_2599393
  have hstable : (prefixWord ++ tailWord_2599393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599393).length < 2 ^ (prefixWord ++ tailWord_2599393).sum := by decide
  have hdescent : baseEnd_2599393 < baseStart_2599393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599397 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 5]
def baseStart_2599397 : Nat := 118140960795 + 2599397 * 2 ^ 59
def prefixEnd_2599397 : Nat := 4983230072969 + 3 ^ 40 * 2599397 * 2
def baseEnd_2599397 : Nat := 148304452539474620109233

theorem tailTrace_2599397 : CollatzResearch.WordTrace tailWord_2599397 prefixEnd_2599397 148304452539474620109233 := by
  unfold tailWord_2599397
  simp only [CollatzResearch.WordTrace]
  refine ⟨94807797363836085508708445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63205198242557390339138963 94807797363836085508708445)
  ·
    refine ⟨35552924011438532065765667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94807797363836085508708445 35552924011438532065765667)
    ·
      refine ⟨53329386017157798098648501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35552924011438532065765667 53329386017157798098648501)
      ·
        refine ⟨4999629939108543571748297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53329386017157798098648501 4999629939108543571748297)
        ·
          refine ⟨3749722454331407678811223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4999629939108543571748297 3749722454331407678811223)
          ·
            refine ⟨5624583681497111518216835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749722454331407678811223 5624583681497111518216835)
            ·
              refine ⟨8436875522245667277325253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624583681497111518216835 8436875522245667277325253)
              ·
                refine ⟨1581914160421062614498485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8436875522245667277325253 1581914160421062614498485)
                ·
                  refine ⟨148304452539474620109233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1581914160421062614498485 148304452539474620109233)
                  ·
                    rfl

theorem cell23_2599397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_2599397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599397 prefixEnd_2599397 := by exact prefixLift 2599397
  have htrace : WordTrace (prefixWord ++ tailWord_2599397) baseStart_2599397 baseEnd_2599397 := by
    simpa [prefixWord, tailWord_2599397, baseEnd_2599397] using wordTrace_append hprefix tailTrace_2599397
  have hstable : (prefixWord ++ tailWord_2599397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599397).length < 2 ^ (prefixWord ++ tailWord_2599397).sum := by decide
  have hdescent : baseEnd_2599397 < baseStart_2599397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599400 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_2599400 : Nat := 118140960795 + 2599400 * 2 ^ 59
def prefixEnd_2599400 : Nat := 4983230072969 + 3 ^ 40 * 2599400 * 2
def baseEnd_2599400 : Nat := 1334741613297235069245583

theorem tailTrace_2599400 : CollatzResearch.WordTrace tailWord_2599400 prefixEnd_2599400 1334741613297235069245583 := by
  unfold tailWord_2599400
  simp only [CollatzResearch.WordTrace]
  refine ⟨47403953391412608510533827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63205271188550144680711769 47403953391412608510533827)
  ·
    refine ⟨71105930087118912765800741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47403953391412608510533827 71105930087118912765800741)
    ·
      refine ⟨13332361891334796143587639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71105930087118912765800741 13332361891334796143587639)
      ·
        refine ⟨19998542837002194215381459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13332361891334796143587639 19998542837002194215381459)
        ·
          refine ⟨29997814255503291323072189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19998542837002194215381459 29997814255503291323072189)
          ·
            refine ⟨11249180345813734246152071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29997814255503291323072189 11249180345813734246152071)
            ·
              refine ⟨16873770518720601369228107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11249180345813734246152071 16873770518720601369228107)
              ·
                refine ⟨25310655778080902053842161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16873770518720601369228107 25310655778080902053842161)
                ·
                  refine ⟨18982991833560676540381621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25310655778080902053842161 18982991833560676540381621)
                  ·
                    refine ⟨1779655484396313425660777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18982991833560676540381621 1779655484396313425660777)
                    ·
                      refine ⟨1334741613297235069245583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779655484396313425660777 1334741613297235069245583)
                      ·
                        rfl

theorem cell23_2599400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_2599400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599400 prefixEnd_2599400 := by exact prefixLift 2599400
  have htrace : WordTrace (prefixWord ++ tailWord_2599400) baseStart_2599400 baseEnd_2599400 := by
    simpa [prefixWord, tailWord_2599400, baseEnd_2599400] using wordTrace_append hprefix tailTrace_2599400
  have hstable : (prefixWord ++ tailWord_2599400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599400).length < 2 ^ (prefixWord ++ tailWord_2599400).sum := by decide
  have hdescent : baseEnd_2599400 < baseStart_2599400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599450 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_2599450 : Nat := 118140960795 + 2599450 * 2 ^ 59
def prefixEnd_2599450 : Nat := 4983230072969 + 3 ^ 40 * 2599450 * 2
def baseEnd_2599450 : Nat := 1334767287329959873620353

theorem tailTrace_2599450 : CollatzResearch.WordTrace tailWord_2599450 prefixEnd_2599450 1334767287329959873620353 := by
  unfold tailWord_2599450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23702432608161018890096951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63206486955096050373591869 23702432608161018890096951)
  ·
    refine ⟨35553648912241528335145427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23702432608161018890096951 35553648912241528335145427)
    ·
      refine ⟨53330473368362292502718141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35553648912241528335145427 53330473368362292502718141)
      ·
        refine ⟨19998927513135859688519303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53330473368362292502718141 19998927513135859688519303)
        ·
          refine ⟨29998391269703789532778955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19998927513135859688519303 29998391269703789532778955)
          ·
            refine ⟨44997586904555684299168433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29998391269703789532778955 44997586904555684299168433)
            ·
              refine ⟨33748190178416763224376325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44997586904555684299168433 33748190178416763224376325)
              ·
                refine ⟨6327785658453143104570561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33748190178416763224376325 6327785658453143104570561)
                ·
                  refine ⟨4745839243839857328427921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327785658453143104570561 4745839243839857328427921)
                  ·
                    refine ⟨3559379432879892996320941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4745839243839857328427921 3559379432879892996320941)
                    ·
                      refine ⟨1334767287329959873620353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3559379432879892996320941 1334767287329959873620353)
                      ·
                        rfl

theorem cell23_2599450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_2599450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599450 prefixEnd_2599450 := by exact prefixLift 2599450
  have htrace : WordTrace (prefixWord ++ tailWord_2599450) baseStart_2599450 baseEnd_2599450 := by
    simpa [prefixWord, tailWord_2599450, baseEnd_2599450] using wordTrace_append hprefix tailTrace_2599450
  have hstable : (prefixWord ++ tailWord_2599450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599450).length < 2 ^ (prefixWord ++ tailWord_2599450).sum := by decide
  have hdescent : baseEnd_2599450 < baseStart_2599450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599457 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2599457 : Nat := 118140960795 + 2599457 * 2 ^ 59
def prefixEnd_2599457 : Nat := 4983230072969 + 3 ^ 40 * 2599457 * 2
def baseEnd_2599457 : Nat := 444923627231513782077607

theorem tailTrace_2599457 : CollatzResearch.WordTrace tailWord_2599457 prefixEnd_2599457 444923627231513782077607 := by
  unfold tailWord_2599457
  simp only [CollatzResearch.WordTrace]
  refine ⟨94809985743618715755892625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63206657162412477170595083 94809985743618715755892625)
  ·
    refine ⟨71107489307714036816919469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94809985743618715755892625 71107489307714036816919469)
    ·
      refine ⟨26665308490392763806344801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71107489307714036816919469 26665308490392763806344801)
      ·
        refine ⟨19998981367794572854758601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26665308490392763806344801 19998981367794572854758601)
        ·
          refine ⟨14999236025845929641068951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19998981367794572854758601 14999236025845929641068951)
          ·
            refine ⟨22498854038768894461603427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14999236025845929641068951 22498854038768894461603427)
            ·
              refine ⟨33748281058153341692405141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22498854038768894461603427 33748281058153341692405141)
              ·
                refine ⟨1581950674600937891831491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33748281058153341692405141 1581950674600937891831491)
                ·
                  refine ⟨2372926011901406837747237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581950674600937891831491 2372926011901406837747237)
                  ·
                    refine ⟨444923627231513782077607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372926011901406837747237 444923627231513782077607)
                    ·
                      rfl

theorem cell23_2599457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2599457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599457 prefixEnd_2599457 := by exact prefixLift 2599457
  have htrace : WordTrace (prefixWord ++ tailWord_2599457) baseStart_2599457 baseEnd_2599457 := by
    simpa [prefixWord, tailWord_2599457, baseEnd_2599457] using wordTrace_append hprefix tailTrace_2599457
  have hstable : (prefixWord ++ tailWord_2599457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599457).length < 2 ^ (prefixWord ++ tailWord_2599457).sum := by decide
  have hdescent : baseEnd_2599457 < baseStart_2599457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599500 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_2599500 : Nat := 118140960795 + 2599500 * 2 ^ 59
def prefixEnd_2599500 : Nat := 4983230072969 + 3 ^ 40 * 2599500 * 2
def baseEnd_2599500 : Nat := 444930987120894892665041

theorem tailTrace_2599500 : CollatzResearch.WordTrace tailWord_2599500 prefixEnd_2599500 444930987120894892665041 := by
  unfold tailWord_2599500
  simp only [CollatzResearch.WordTrace]
  refine ⟨47405777041231467049853977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63207702721641956066471969 47405777041231467049853977)
  ·
    refine ⟨35554332780923600287390483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47405777041231467049853977 35554332780923600287390483)
    ·
      refine ⟨53331499171385400431085725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35554332780923600287390483 53331499171385400431085725)
      ·
        refine ⟨19999312189269525161657147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53331499171385400431085725 19999312189269525161657147)
        ·
          refine ⟨29998968283904287742485721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19999312189269525161657147 29998968283904287742485721)
          ·
            refine ⟨22499226212928215806864291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29998968283904287742485721 22499226212928215806864291)
            ·
              refine ⟨33748839319392323710296437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22499226212928215806864291 33748839319392323710296437)
              ·
                refine ⟨3163953686193030347840291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33748839319392323710296437 3163953686193030347840291)
                ·
                  refine ⟨4745930529289545521760437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163953686193030347840291 4745930529289545521760437)
                  ·
                    refine ⟨444930987120894892665041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4745930529289545521760437 444930987120894892665041)
                    ·
                      rfl

theorem cell23_2599500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_2599500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599500 prefixEnd_2599500 := by exact prefixLift 2599500
  have htrace : WordTrace (prefixWord ++ tailWord_2599500) baseStart_2599500 baseEnd_2599500 := by
    simpa [prefixWord, tailWord_2599500, baseEnd_2599500] using wordTrace_append hprefix tailTrace_2599500
  have hstable : (prefixWord ++ tailWord_2599500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599500).length < 2 ^ (prefixWord ++ tailWord_2599500).sum := by decide
  have hdescent : baseEnd_2599500 < baseStart_2599500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599530 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2599530 : Nat := 118140960795 + 2599530 * 2 ^ 59
def prefixEnd_2599530 : Nat := 4983230072969 + 3 ^ 40 * 2599530 * 2
def baseEnd_2599530 : Nat := 444936121927439853539995

theorem tailTrace_2599530 : CollatzResearch.WordTrace tailWord_2599530 prefixEnd_2599530 444936121927439853539995 := by
  unfold tailWord_2599530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23703162068088562305825011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63208432181569499482200029 23703162068088562305825011)
  ·
    refine ⟨35554743102132843458737517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23703162068088562305825011 35554743102132843458737517)
    ·
      refine ⟨13333028663299816297026569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35554743102132843458737517 13333028663299816297026569)
      ·
        refine ⟨9999771497474862222769927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13333028663299816297026569 9999771497474862222769927)
        ·
          refine ⟨14999657246212293334154891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9999771497474862222769927 14999657246212293334154891)
          ·
            refine ⟨22499485869318440001232337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14999657246212293334154891 22499485869318440001232337)
            ·
              refine ⟨16874614401988830000924253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22499485869318440001232337 16874614401988830000924253)
              ·
                refine ⟨6327980400745811250346595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16874614401988830000924253 6327980400745811250346595)
                ·
                  refine ⟨9491970601118716875519893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6327980400745811250346595 9491970601118716875519893)
                  ·
                    refine ⟨444936121927439853539995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9491970601118716875519893 444936121927439853539995)
                    ·
                      rfl

theorem cell23_2599530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2599530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599530 prefixEnd_2599530 := by exact prefixLift 2599530
  have htrace : WordTrace (prefixWord ++ tailWord_2599530) baseStart_2599530 baseEnd_2599530 := by
    simpa [prefixWord, tailWord_2599530, baseEnd_2599530] using wordTrace_append hprefix tailTrace_2599530
  have hstable : (prefixWord ++ tailWord_2599530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599530).length < 2 ^ (prefixWord ++ tailWord_2599530).sum := by decide
  have hdescent : baseEnd_2599530 < baseStart_2599530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599534 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_2599534 : Nat := 118140960795 + 2599534 * 2 ^ 59
def prefixEnd_2599534 : Nat := 4983230072969 + 3 ^ 40 * 2599534 * 2
def baseEnd_2599534 : Nat := 444936806568312514989989

theorem tailTrace_2599534 : CollatzResearch.WordTrace tailWord_2599534 prefixEnd_2599534 444936806568312514989989 := by
  unfold tailWord_2599534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11851599270542469738305707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63208529442893171937630437 11851599270542469738305707)
  ·
    refine ⟨17777398905813704607458561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11851599270542469738305707 17777398905813704607458561)
    ·
      refine ⟨13333049179360278455593921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17777398905813704607458561 13333049179360278455593921)
      ·
        refine ⟨9999786884520208841695441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13333049179360278455593921 9999786884520208841695441)
        ·
          refine ⟨7499840163390156631271581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9999786884520208841695441 7499840163390156631271581)
          ·
            refine ⟨2812440061271308736726843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7499840163390156631271581 2812440061271308736726843)
            ·
              refine ⟨4218660091906963105090265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812440061271308736726843 4218660091906963105090265)
              ·
                refine ⟨3163995068930222328817699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4218660091906963105090265 3163995068930222328817699)
                ·
                  refine ⟨4745992603395333493226549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163995068930222328817699 4745992603395333493226549)
                  ·
                    refine ⟨444936806568312514989989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4745992603395333493226549 444936806568312514989989)
                    ·
                      rfl

theorem cell23_2599534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_2599534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599534 prefixEnd_2599534 := by exact prefixLift 2599534
  have htrace : WordTrace (prefixWord ++ tailWord_2599534) baseStart_2599534 baseEnd_2599534 := by
    simpa [prefixWord, tailWord_2599534, baseEnd_2599534] using wordTrace_append hprefix tailTrace_2599534
  have hstable : (prefixWord ++ tailWord_2599534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599534).length < 2 ^ (prefixWord ++ tailWord_2599534).sum := by decide
  have hdescent : baseEnd_2599534 < baseStart_2599534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599541 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2599541 : Nat := 118140960795 + 2599541 * 2 ^ 59
def prefixEnd_2599541 : Nat := 4983230072969 + 3 ^ 40 * 2599541 * 2
def baseEnd_2599541 : Nat := 1334814014069519017582435

theorem tailTrace_2599541 : CollatzResearch.WordTrace tailWord_2599541 prefixEnd_2599541 1334814014069519017582435 := by
  unfold tailWord_2599541
  simp only [CollatzResearch.WordTrace]
  refine ⟨94813049475314398101950477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63208699650209598734633651 94813049475314398101950477)
  ·
    refine ⟨35554893553242899288231429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94813049475314398101950477 35554893553242899288231429)
    ·
      refine ⟨6666542541233043616543393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35554893553242899288231429 6666542541233043616543393)
      ·
        refine ⟨4999906905924782712407545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6666542541233043616543393 4999906905924782712407545)
        ·
          refine ⟨3749930179443587034305659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4999906905924782712407545 3749930179443587034305659)
          ·
            refine ⟨5624895269165380551458489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749930179443587034305659 5624895269165380551458489)
            ·
              refine ⟨4218671451874035413593867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5624895269165380551458489 4218671451874035413593867)
              ·
                refine ⟨6328007177811053120390801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218671451874035413593867 6328007177811053120390801)
                ·
                  refine ⟨4746005383358289840293101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6328007177811053120390801 4746005383358289840293101)
                  ·
                    refine ⟨1779752018759358690109913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4746005383358289840293101 1779752018759358690109913)
                    ·
                      refine ⟨1334814014069519017582435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1779752018759358690109913 1334814014069519017582435)
                      ·
                        rfl

theorem cell23_2599541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2599541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599541 prefixEnd_2599541 := by exact prefixLift 2599541
  have htrace : WordTrace (prefixWord ++ tailWord_2599541) baseStart_2599541 baseEnd_2599541 := by
    simpa [prefixWord, tailWord_2599541, baseEnd_2599541] using wordTrace_append hprefix tailTrace_2599541
  have hstable : (prefixWord ++ tailWord_2599541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599541).length < 2 ^ (prefixWord ++ tailWord_2599541).sum := by decide
  have hdescent : baseEnd_2599541 < baseStart_2599541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599543 : List Nat := [1, 1, 3, 1, 1, 3, 4, 9]
def baseStart_2599543 : Nat := 118140960795 + 2599543 * 2 ^ 59
def prefixEnd_2599543 : Nat := 4983230072969 + 3 ^ 40 * 2599543 * 2
def baseEnd_2599543 : Nat := 49437594112252889250275

theorem tailTrace_2599543 : CollatzResearch.WordTrace tailWord_2599543 prefixEnd_2599543 49437594112252889250275 := by
  unfold tailWord_2599543
  simp only [CollatzResearch.WordTrace]
  refine ⟨94813122421307152443523283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63208748280871434962348855 94813122421307152443523283)
  ·
    refine ⟨142219683631960728665284925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94813122421307152443523283 142219683631960728665284925)
    ·
      refine ⟨53332381361985273249481847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142219683631960728665284925 53332381361985273249481847)
      ·
        refine ⟨79998572042977909874222771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53332381361985273249481847 79998572042977909874222771)
        ·
          refine ⟨119997858064466864811334157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79998572042977909874222771 119997858064466864811334157)
          ·
            refine ⟨44999196774175074304250309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119997858064466864811334157 44999196774175074304250309)
            ·
              refine ⟨8437349395157826432046933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44999196774175074304250309 8437349395157826432046933)
              ·
                refine ⟨49437594112252889250275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8437349395157826432046933 49437594112252889250275)
                ·
                  rfl

theorem cell23_2599543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 9].length) (baseStart_2599543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599543 prefixEnd_2599543 := by exact prefixLift 2599543
  have htrace : WordTrace (prefixWord ++ tailWord_2599543) baseStart_2599543 baseEnd_2599543 := by
    simpa [prefixWord, tailWord_2599543, baseEnd_2599543] using wordTrace_append hprefix tailTrace_2599543
  have hstable : (prefixWord ++ tailWord_2599543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599543).length < 2 ^ (prefixWord ++ tailWord_2599543).sum := by decide
  have hdescent : baseEnd_2599543 < baseStart_2599543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599557 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_2599557 : Nat := 118140960795 + 2599557 * 2 ^ 59
def prefixEnd_2599557 : Nat := 4983230072969 + 3 ^ 40 * 2599557 * 2
def baseEnd_2599557 : Nat := 1334822229759990954982361

theorem tailTrace_2599557 : CollatzResearch.WordTrace tailWord_2599557 prefixEnd_2599557 1334822229759990954982361 := by
  unfold tailWord_2599557
  simp only [CollatzResearch.WordTrace]
  refine ⟨94813633043256432834532925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63209088695504288556355283 94813633043256432834532925)
  ·
    refine ⟨35555112391221162312949847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94813633043256432834532925 35555112391221162312949847)
    ·
      refine ⟨53332668586831743469424771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35555112391221162312949847 53332668586831743469424771)
      ·
        refine ⟨79999002880247615204137157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53332668586831743469424771 79999002880247615204137157)
        ·
          refine ⟨14999813040046427850775717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79999002880247615204137157 14999813040046427850775717)
          ·
            refine ⟨2812464945008705222020447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14999813040046427850775717 2812464945008705222020447)
            ·
              refine ⟨4218697417513057833030671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812464945008705222020447 4218697417513057833030671)
              ·
                refine ⟨6328046126269586749546007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218697417513057833030671 6328046126269586749546007)
                ·
                  refine ⟨9492069189404380124319011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6328046126269586749546007 9492069189404380124319011)
                  ·
                    refine ⟨14238103784106570186478517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9492069189404380124319011 14238103784106570186478517)
                    ·
                      refine ⟨1334822229759990954982361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14238103784106570186478517 1334822229759990954982361)
                      ·
                        rfl

theorem cell23_2599557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_2599557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599557 prefixEnd_2599557 := by exact prefixLift 2599557
  have htrace : WordTrace (prefixWord ++ tailWord_2599557) baseStart_2599557 baseEnd_2599557 := by
    simpa [prefixWord, tailWord_2599557, baseEnd_2599557] using wordTrace_append hprefix tailTrace_2599557
  have hstable : (prefixWord ++ tailWord_2599557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599557).length < 2 ^ (prefixWord ++ tailWord_2599557).sum := by decide
  have hdescent : baseEnd_2599557 < baseStart_2599557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599563 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_2599563 : Nat := 118140960795 + 2599563 * 2 ^ 59
def prefixEnd_2599563 : Nat := 4983230072969 + 3 ^ 40 * 2599563 * 2
def baseEnd_2599563 : Nat := 1334825310643917931507333

theorem tailTrace_2599563 : CollatzResearch.WordTrace tailWord_2599563 prefixEnd_2599563 1334825310643917931507333 := by
  unfold tailWord_2599563
  simp only [CollatzResearch.WordTrace]
  refine ⟨94813851881234695859251343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63209234587489797239500895 94813851881234695859251343)
  ·
    refine ⟨142220777821852043788877015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94813851881234695859251343 142220777821852043788877015)
    ·
      refine ⟨213331166732778065683315523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142220777821852043788877015 213331166732778065683315523)
      ·
        refine ⟨319996750099167098524973285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213331166732778065683315523 319996750099167098524973285)
        ·
          refine ⟨59999390643593830973432491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319996750099167098524973285 59999390643593830973432491)
          ·
            refine ⟨89999085965390746460148737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59999390643593830973432491 89999085965390746460148737)
            ·
              refine ⟨67499314474043059845111553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89999085965390746460148737 67499314474043059845111553)
              ·
                refine ⟨50624485855532294883833665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67499314474043059845111553 50624485855532294883833665)
                ·
                  refine ⟨37968364391649221162875249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50624485855532294883833665 37968364391649221162875249)
                  ·
                    refine ⟨28476273293736915872156437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37968364391649221162875249 28476273293736915872156437)
                    ·
                      refine ⟨1334825310643917931507333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28476273293736915872156437 1334825310643917931507333)
                      ·
                        rfl

theorem cell23_2599563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_2599563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599563 prefixEnd_2599563 := by exact prefixLift 2599563
  have htrace : WordTrace (prefixWord ++ tailWord_2599563) baseStart_2599563 baseEnd_2599563 := by
    simpa [prefixWord, tailWord_2599563, baseEnd_2599563] using wordTrace_append hprefix tailTrace_2599563
  have hstable : (prefixWord ++ tailWord_2599563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599563).length < 2 ^ (prefixWord ++ tailWord_2599563).sum := by decide
  have hdescent : baseEnd_2599563 < baseStart_2599563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599593 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_2599593 : Nat := 118140960795 + 2599593 * 2 ^ 59
def prefixEnd_2599593 : Nat := 4983230072969 + 3 ^ 40 * 2599593 * 2
def baseEnd_2599593 : Nat := 1334840715063552814132195

theorem tailTrace_2599593 : CollatzResearch.WordTrace tailWord_2599593 prefixEnd_2599593 1334840715063552814132195 := by
  unfold tailWord_2599593
  simp only [CollatzResearch.WordTrace]
  refine ⟨94814946071126010982843433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63209964047417340655228955 94814946071126010982843433)
  ·
    refine ⟨71111209553344508237132575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94814946071126010982843433 71111209553344508237132575)
    ·
      refine ⟨106666814330016762355698863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71111209553344508237132575 106666814330016762355698863)
      ·
        refine ⟨160000221495025143533548295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106666814330016762355698863 160000221495025143533548295)
        ·
          refine ⟨240000332242537715300322443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160000221495025143533548295 240000332242537715300322443)
          ·
            refine ⟨360000498363806572950483665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240000332242537715300322443 360000498363806572950483665)
            ·
              refine ⟨270000373772854929712862749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360000498363806572950483665 270000373772854929712862749)
              ·
                refine ⟨101250140164820598642323531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270000373772854929712862749 101250140164820598642323531)
                ·
                  refine ⟨151875210247230897963485297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101250140164820598642323531 151875210247230897963485297)
                  ·
                    refine ⟨113906407685423173472613973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151875210247230897963485297 113906407685423173472613973)
                    ·
                      refine ⟨1334840715063552814132195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 113906407685423173472613973 1334840715063552814132195)
                      ·
                        rfl

theorem cell23_2599593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_2599593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599593 prefixEnd_2599593 := by exact prefixLift 2599593
  have htrace : WordTrace (prefixWord ++ tailWord_2599593) baseStart_2599593 baseEnd_2599593 := by
    simpa [prefixWord, tailWord_2599593, baseEnd_2599593] using wordTrace_append hprefix tailTrace_2599593
  have hstable : (prefixWord ++ tailWord_2599593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599593).length < 2 ^ (prefixWord ++ tailWord_2599593).sum := by decide
  have hdescent : baseEnd_2599593 < baseStart_2599593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599714 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2599714 : Nat := 118140960795 + 2599714 * 2 ^ 59
def prefixEnd_2599714 : Nat := 4983230072969 + 3 ^ 40 * 2599714 * 2
def baseEnd_2599714 : Nat := 444967615407582280239713

theorem tailTrace_2599714 : CollatzResearch.WordTrace tailWord_2599714 prefixEnd_2599714 444967615407582280239713 := by
  unfold tailWord_2599714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23704839825921912161999549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63212906202458432431998797 23704839825921912161999549)
  ·
    refine ⟨8889314934720717060749831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23704839825921912161999549 8889314934720717060749831)
    ·
      refine ⟨13333972402081075591124747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8889314934720717060749831 13333972402081075591124747)
      ·
        refine ⟨20000958603121613386687121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13333972402081075591124747 20000958603121613386687121)
        ·
          refine ⟨15000718952341210040015341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20000958603121613386687121 15000718952341210040015341)
          ·
            refine ⟨5625269607127953765005753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15000718952341210040015341 5625269607127953765005753)
            ·
              refine ⟨4218952205345965323754315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5625269607127953765005753 4218952205345965323754315)
              ·
                refine ⟨6328428308018947985631473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218952205345965323754315 6328428308018947985631473)
                ·
                  refine ⟨4746321231014210989223605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6328428308018947985631473 4746321231014210989223605)
                  ·
                    refine ⟨444967615407582280239713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4746321231014210989223605 444967615407582280239713)
                    ·
                      rfl

theorem cell23_2599714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2599714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599714 prefixEnd_2599714 := by exact prefixLift 2599714
  have htrace : WordTrace (prefixWord ++ tailWord_2599714) baseStart_2599714 baseEnd_2599714 := by
    simpa [prefixWord, tailWord_2599714, baseEnd_2599714] using wordTrace_append hprefix tailTrace_2599714
  have hstable : (prefixWord ++ tailWord_2599714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599714).length < 2 ^ (prefixWord ++ tailWord_2599714).sum := by decide
  have hdescent : baseEnd_2599714 < baseStart_2599714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599801 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2599801 : Nat := 118140960795 + 2599801 * 2 ^ 59
def prefixEnd_2599801 : Nat := 4983230072969 + 3 ^ 40 * 2599801 * 2
def baseEnd_2599801 : Nat := 1334947519039688000331239

theorem tailTrace_2599801 : CollatzResearch.WordTrace tailWord_2599801 prefixEnd_2599801 1334947519039688000331239 := by
  unfold tailWord_2599801
  simp only [CollatzResearch.WordTrace]
  refine ⟨94822532454372462506415257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63215021636248308337610171 94822532454372462506415257)
  ·
    refine ⟨71116899340779346879811443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94822532454372462506415257 71116899340779346879811443)
    ·
      refine ⟨106675349011169020319717165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71116899340779346879811443 106675349011169020319717165)
      ·
        refine ⟨40003255879188382619893937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106675349011169020319717165 40003255879188382619893937)
        ·
          refine ⟨30002441909391286964920453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40003255879188382619893937 30002441909391286964920453)
          ·
            refine ⟨5625457858010866305922585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30002441909391286964920453 5625457858010866305922585)
            ·
              refine ⟨4219093393508149729441939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5625457858010866305922585 4219093393508149729441939)
              ·
                refine ⟨6328640090262224594162909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219093393508149729441939 6328640090262224594162909)
                ·
                  refine ⟨2373240033848334222811091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6328640090262224594162909 2373240033848334222811091)
                  ·
                    refine ⟨3559860050772501334216637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2373240033848334222811091 3559860050772501334216637)
                    ·
                      refine ⟨1334947519039688000331239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3559860050772501334216637 1334947519039688000331239)
                      ·
                        rfl

theorem cell23_2599801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2599801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599801 prefixEnd_2599801 := by exact prefixLift 2599801
  have htrace : WordTrace (prefixWord ++ tailWord_2599801) baseStart_2599801 baseEnd_2599801 := by
    simpa [prefixWord, tailWord_2599801, baseEnd_2599801] using wordTrace_append hprefix tailTrace_2599801
  have hstable : (prefixWord ++ tailWord_2599801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599801).length < 2 ^ (prefixWord ++ tailWord_2599801).sum := by decide
  have hdescent : baseEnd_2599801 < baseStart_2599801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599807 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_2599807 : Nat := 118140960795 + 2599807 * 2 ^ 59
def prefixEnd_2599807 : Nat := 4983230072969 + 3 ^ 40 * 2599807 * 2
def baseEnd_2599807 : Nat := 1334950599923614976856211

theorem tailTrace_2599807 : CollatzResearch.WordTrace tailWord_2599807 prefixEnd_2599807 1334950599923614976856211 := by
  unfold tailWord_2599807
  simp only [CollatzResearch.WordTrace]
  refine ⟨94822751292350725531133675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63215167528233817020755783 94822751292350725531133675)
  ·
    refine ⟨142234126938526088296700513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94822751292350725531133675 142234126938526088296700513)
    ·
      refine ⟨106675595203894566222525385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142234126938526088296700513 106675595203894566222525385)
      ·
        refine ⟨80006696402920924666894039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106675595203894566222525385 80006696402920924666894039)
        ·
          refine ⟨120010044604381387000341059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80006696402920924666894039 120010044604381387000341059)
          ·
            refine ⟨180015066906572080500511589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120010044604381387000341059 180015066906572080500511589)
            ·
              refine ⟨33752825044982265093845923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180015066906572080500511589 33752825044982265093845923)
              ·
                refine ⟨50629237567473397640768885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33752825044982265093845923 50629237567473397640768885)
                ·
                  refine ⟨4746491021950631028822083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50629237567473397640768885 4746491021950631028822083)
                  ·
                    refine ⟨7119736532925946543233125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4746491021950631028822083 7119736532925946543233125)
                    ·
                      refine ⟨1334950599923614976856211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7119736532925946543233125 1334950599923614976856211)
                      ·
                        rfl

theorem cell23_2599807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_2599807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599807 prefixEnd_2599807 := by exact prefixLift 2599807
  have htrace : WordTrace (prefixWord ++ tailWord_2599807) baseStart_2599807 baseEnd_2599807 := by
    simpa [prefixWord, tailWord_2599807, baseEnd_2599807] using wordTrace_append hprefix tailTrace_2599807
  have hstable : (prefixWord ++ tailWord_2599807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599807).length < 2 ^ (prefixWord ++ tailWord_2599807).sum := by decide
  have hdescent : baseEnd_2599807 < baseStart_2599807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599841 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2599841 : Nat := 118140960795 + 2599841 * 2 ^ 59
def prefixEnd_2599841 : Nat := 4983230072969 + 3 ^ 40 * 2599841 * 2
def baseEnd_2599841 : Nat := 1334968058265867843831055

theorem tailTrace_2599841 : CollatzResearch.WordTrace tailWord_2599841 prefixEnd_2599841 1334968058265867843831055 := by
  unfold tailWord_2599841
  simp only [CollatzResearch.WordTrace]
  refine ⟨94823991374227549337871377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63215994249485032891914251 94823991374227549337871377)
  ·
    refine ⟨71117993530670662003403533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94823991374227549337871377 71117993530670662003403533)
    ·
      refine ⟨26669247574001498251276325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71117993530670662003403533 26669247574001498251276325)
      ·
        refine ⟨5000483920125280922114311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26669247574001498251276325 5000483920125280922114311)
        ·
          refine ⟨7500725880187921383171467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000483920125280922114311 7500725880187921383171467)
          ·
            refine ⟨11251088820281882074757201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500725880187921383171467 11251088820281882074757201)
            ·
              refine ⟨8438316615211411556067901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11251088820281882074757201 8438316615211411556067901)
              ·
                refine ⟨3164368730704279333525463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8438316615211411556067901 3164368730704279333525463)
                ·
                  refine ⟨4746553096056419000288195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164368730704279333525463 4746553096056419000288195)
                  ·
                    refine ⟨7119829644084628500432293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4746553096056419000288195 7119829644084628500432293)
                    ·
                      refine ⟨1334968058265867843831055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7119829644084628500432293 1334968058265867843831055)
                      ·
                        rfl

theorem cell23_2599841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2599841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599841 prefixEnd_2599841 := by exact prefixLift 2599841
  have htrace : WordTrace (prefixWord ++ tailWord_2599841) baseStart_2599841 baseEnd_2599841 := by
    simpa [prefixWord, tailWord_2599841, baseEnd_2599841] using wordTrace_append hprefix tailTrace_2599841
  have hstable : (prefixWord ++ tailWord_2599841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599841).length < 2 ^ (prefixWord ++ tailWord_2599841).sum := by decide
  have hdescent : baseEnd_2599841 < baseStart_2599841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599844 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_2599844 : Nat := 118140960795 + 2599844 * 2 ^ 59
def prefixEnd_2599844 : Nat := 4983230072969 + 3 ^ 40 * 2599844 * 2
def baseEnd_2599844 : Nat := 1334969598707831332093541

theorem tailTrace_2599844 : CollatzResearch.WordTrace tailWord_2599844 prefixEnd_2599844 1334969598707831332093541 := by
  unfold tailWord_2599844
  simp only [CollatzResearch.WordTrace]
  refine ⟨47412050396608340425115293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63216067195477787233487057 47412050396608340425115293)
  ·
    refine ⟨17779518898728127659418235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47412050396608340425115293 17779518898728127659418235)
    ·
      refine ⟨26669278348092191489127353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17779518898728127659418235 26669278348092191489127353)
      ·
        refine ⟨20001958761069143616845515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26669278348092191489127353 20001958761069143616845515)
        ·
          refine ⟨30002938141603715425268273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20001958761069143616845515 30002938141603715425268273)
          ·
            refine ⟨22502203606202786568951205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30002938141603715425268273 22502203606202786568951205)
            ·
              refine ⟨4219163176163022481678351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22502203606202786568951205 4219163176163022481678351)
              ·
                refine ⟨6328744764244533722517527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219163176163022481678351 6328744764244533722517527)
                ·
                  refine ⟨9493117146366800583776291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6328744764244533722517527 9493117146366800583776291)
                  ·
                    refine ⟨14239675719550200875664437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9493117146366800583776291 14239675719550200875664437)
                    ·
                      refine ⟨1334969598707831332093541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14239675719550200875664437 1334969598707831332093541)
                      ·
                        rfl

theorem cell23_2599844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_2599844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599844 prefixEnd_2599844 := by exact prefixLift 2599844
  have htrace : WordTrace (prefixWord ++ tailWord_2599844) baseStart_2599844 baseEnd_2599844 := by
    simpa [prefixWord, tailWord_2599844, baseEnd_2599844] using wordTrace_append hprefix tailTrace_2599844
  have hstable : (prefixWord ++ tailWord_2599844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599844).length < 2 ^ (prefixWord ++ tailWord_2599844).sum := by decide
  have hdescent : baseEnd_2599844 < baseStart_2599844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599885 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2599885 : Nat := 118140960795 + 2599885 * 2 ^ 59
def prefixEnd_2599885 : Nat := 4983230072969 + 3 ^ 40 * 2599885 * 2
def baseEnd_2599885 : Nat := 444996883804888557226951

theorem tailTrace_2599885 : CollatzResearch.WordTrace tailWord_2599885 prefixEnd_2599885 444996883804888557226951 := by
  unfold tailWord_2599885
  simp only [CollatzResearch.WordTrace]
  refine ⟨94825596186068144852473109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63217064124045429901648739 94825596186068144852473109)
  ·
    refine ⟨4444949821221944289959677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94825596186068144852473109 4444949821221944289959677)
    ·
      refine ⟨1666856182958229108734879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4444949821221944289959677 1666856182958229108734879)
      ·
        refine ⟨2500284274437343663102319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666856182958229108734879 2500284274437343663102319)
        ·
          refine ⟨3750426411656015494653479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500284274437343663102319 3750426411656015494653479)
          ·
            refine ⟨5625639617484023241980219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750426411656015494653479 5625639617484023241980219)
            ·
              refine ⟨8438459426226034862970329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625639617484023241980219 8438459426226034862970329)
              ·
                refine ⟨6328844569669526147227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438459426226034862970329 6328844569669526147227747)
                ·
                  refine ⟨9493266854504289220841621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6328844569669526147227747 9493266854504289220841621)
                  ·
                    refine ⟨444996883804888557226951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9493266854504289220841621 444996883804888557226951)
                    ·
                      rfl

theorem cell23_2599885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2599885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599885 prefixEnd_2599885 := by exact prefixLift 2599885
  have htrace : WordTrace (prefixWord ++ tailWord_2599885) baseStart_2599885 baseEnd_2599885 := by
    simpa [prefixWord, tailWord_2599885, baseEnd_2599885] using wordTrace_append hprefix tailTrace_2599885
  have hstable : (prefixWord ++ tailWord_2599885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599885).length < 2 ^ (prefixWord ++ tailWord_2599885).sum := by decide
  have hdescent : baseEnd_2599885 < baseStart_2599885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599914 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2599914 : Nat := 118140960795 + 2599914 * 2 ^ 59
def prefixEnd_2599914 : Nat := 4983230072969 + 3 ^ 40 * 2599914 * 2
def baseEnd_2599914 : Nat := 1335005542353646058218219

theorem tailTrace_2599914 : CollatzResearch.WordTrace tailWord_2599914 prefixEnd_2599914 1335005542353646058218219 := by
  unfold tailWord_2599914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23706663475740770701319699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63217769268642055203519197 23706663475740770701319699)
  ·
    refine ⟨35559995213611156051979549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23706663475740770701319699 35559995213611156051979549)
    ·
      refine ⟨13334998205104183519492331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35559995213611156051979549 13334998205104183519492331)
      ·
        refine ⟨20002497307656275279238497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13334998205104183519492331 20002497307656275279238497)
        ·
          refine ⟨15001872980742206459428873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20002497307656275279238497 15001872980742206459428873)
          ·
            refine ⟨11251404735556654844571655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15001872980742206459428873 11251404735556654844571655)
            ·
              refine ⟨16877107103334982266857483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11251404735556654844571655 16877107103334982266857483)
              ·
                refine ⟨25315660655002473400286225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16877107103334982266857483 25315660655002473400286225)
                ·
                  refine ⟨18986745491251855050214669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25315660655002473400286225 18986745491251855050214669)
                  ·
                    refine ⟨7120029559219445643830501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18986745491251855050214669 7120029559219445643830501)
                    ·
                      refine ⟨1335005542353646058218219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7120029559219445643830501 1335005542353646058218219)
                      ·
                        rfl

theorem cell23_2599914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2599914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599914 prefixEnd_2599914 := by exact prefixLift 2599914
  have htrace : WordTrace (prefixWord ++ tailWord_2599914) baseStart_2599914 baseEnd_2599914 := by
    simpa [prefixWord, tailWord_2599914, baseEnd_2599914] using wordTrace_append hprefix tailTrace_2599914
  have hstable : (prefixWord ++ tailWord_2599914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599914).length < 2 ^ (prefixWord ++ tailWord_2599914).sum := by decide
  have hdescent : baseEnd_2599914 < baseStart_2599914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599925 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2599925 : Nat := 118140960795 + 2599925 * 2 ^ 59
def prefixEnd_2599925 : Nat := 4983230072969 + 3 ^ 40 * 2599925 * 2
def baseEnd_2599925 : Nat := 1335011190640845515180669

theorem tailTrace_2599925 : CollatzResearch.WordTrace tailWord_2599925 prefixEnd_2599925 1335011190640845515180669 := by
  unfold tailWord_2599925
  simp only [CollatzResearch.WordTrace]
  refine ⟨94827055105923231683929229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63218036737282154455952819 94827055105923231683929229)
  ·
    refine ⟨35560145664721211881473461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94827055105923231683929229 35560145664721211881473461)
    ·
      refine ⟨3333763656067613613888137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35560145664721211881473461 3333763656067613613888137)
      ·
        refine ⟨2500322742050710210416103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3333763656067613613888137 2500322742050710210416103)
        ·
          refine ⟨3750484113076065315624155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500322742050710210416103 3750484113076065315624155)
          ·
            refine ⟨5625726169614097973436233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750484113076065315624155 5625726169614097973436233)
            ·
              refine ⟨4219294627210573480077175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5625726169614097973436233 4219294627210573480077175)
              ·
                refine ⟨6328941940815860220115763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219294627210573480077175 6328941940815860220115763)
                ·
                  refine ⟨9493412911223790330173645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6328941940815860220115763 9493412911223790330173645)
                  ·
                    refine ⟨3560029841708921373815117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9493412911223790330173645 3560029841708921373815117)
                    ·
                      refine ⟨1335011190640845515180669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560029841708921373815117 1335011190640845515180669)
                      ·
                        rfl

theorem cell23_2599925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2599925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599925 prefixEnd_2599925 := by exact prefixLift 2599925
  have htrace : WordTrace (prefixWord ++ tailWord_2599925) baseStart_2599925 baseEnd_2599925 := by
    simpa [prefixWord, tailWord_2599925, baseEnd_2599925] using wordTrace_append hprefix tailTrace_2599925
  have hstable : (prefixWord ++ tailWord_2599925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599925).length < 2 ^ (prefixWord ++ tailWord_2599925).sum := by decide
  have hdescent : baseEnd_2599925 < baseStart_2599925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599931 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 6, 2, 2]
def baseStart_2599931 : Nat := 118140960795 + 2599931 * 2 ^ 59
def prefixEnd_2599931 : Nat := 4983230072969 + 3 ^ 40 * 2599931 * 2
def baseEnd_2599931 : Nat := 1335014271524772491705641

theorem tailTrace_2599931 : CollatzResearch.WordTrace tailWord_2599931 prefixEnd_2599931 1335014271524772491705641 := by
  unfold tailWord_2599931
  simp only [CollatzResearch.WordTrace]
  refine ⟨94827273943901494708647647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63218182629267663139098431 94827273943901494708647647)
  ·
    refine ⟨142240910915852242062971471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94827273943901494708647647 142240910915852242062971471)
    ·
      refine ⟨213361366373778363094457207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142240910915852242062971471 213361366373778363094457207)
      ·
        refine ⟨320042049560667544641685811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213361366373778363094457207 320042049560667544641685811)
        ·
          refine ⟨480063074341001316962528717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320042049560667544641685811 480063074341001316962528717)
          ·
            refine ⟨180023652877875493860948269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480063074341001316962528717 180023652877875493860948269)
            ·
              refine ⟨67508869829203310197855601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180023652877875493860948269 67508869829203310197855601)
              ·
                refine ⟨50631652371902482648391701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67508869829203310197855601 50631652371902482648391701)
                ·
                  refine ⟨2373358704932928874143361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50631652371902482648391701 2373358704932928874143361)
                  ·
                    refine ⟨1780019028699696655607521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373358704932928874143361 1780019028699696655607521)
                    ·
                      refine ⟨1335014271524772491705641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780019028699696655607521 1335014271524772491705641)
                      ·
                        rfl

theorem cell23_2599931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 2, 2].length) (baseStart_2599931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599931 prefixEnd_2599931 := by exact prefixLift 2599931
  have htrace : WordTrace (prefixWord ++ tailWord_2599931) baseStart_2599931 baseEnd_2599931 := by
    simpa [prefixWord, tailWord_2599931, baseEnd_2599931] using wordTrace_append hprefix tailTrace_2599931
  have hstable : (prefixWord ++ tailWord_2599931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599931).length < 2 ^ (prefixWord ++ tailWord_2599931).sum := by decide
  have hdescent : baseEnd_2599931 < baseStart_2599931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599965 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_2599965 : Nat := 118140960795 + 2599965 * 2 ^ 59
def prefixEnd_2599965 : Nat := 4983230072969 + 3 ^ 40 * 2599965 * 2
def baseEnd_2599965 : Nat := 1335031729867025358680485

theorem tailTrace_2599965 : CollatzResearch.WordTrace tailWord_2599965 prefixEnd_2599965 1335031729867025358680485 := by
  unfold tailWord_2599965
  simp only [CollatzResearch.WordTrace]
  refine ⟨94828514025778318515385349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63219009350518879010256899 94828514025778318515385349)
  ·
    refine ⟨17780346379833434721634753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94828514025778318515385349 17780346379833434721634753)
    ·
      refine ⟨13335259784875076041226065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17780346379833434721634753 13335259784875076041226065)
      ·
        refine ⟨10001444838656307030919549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13335259784875076041226065 10001444838656307030919549)
        ·
          refine ⟨3750541814496115136594831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10001444838656307030919549 3750541814496115136594831)
          ·
            refine ⟨5625812721744172704892247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750541814496115136594831 5625812721744172704892247)
            ·
              refine ⟨8438719082616259057338371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625812721744172704892247 8438719082616259057338371)
              ·
                refine ⟨12658078623924388586007557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8438719082616259057338371 12658078623924388586007557)
                ·
                  refine ⟨2373389741985822859876417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12658078623924388586007557 2373389741985822859876417)
                  ·
                    refine ⟨1780042306489367144907313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373389741985822859876417 1780042306489367144907313)
                    ·
                      refine ⟨1335031729867025358680485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780042306489367144907313 1335031729867025358680485)
                      ·
                        rfl

theorem cell23_2599965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_2599965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599965 prefixEnd_2599965 := by exact prefixLift 2599965
  have htrace : WordTrace (prefixWord ++ tailWord_2599965) baseStart_2599965 baseEnd_2599965 := by
    simpa [prefixWord, tailWord_2599965, baseEnd_2599965] using wordTrace_append hprefix tailTrace_2599965
  have hstable : (prefixWord ++ tailWord_2599965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599965).length < 2 ^ (prefixWord ++ tailWord_2599965).sum := by decide
  have hdescent : baseEnd_2599965 < baseStart_2599965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599971 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 5]
def baseStart_2599971 : Nat := 118140960795 + 2599971 * 2 ^ 59
def prefixEnd_2599971 : Nat := 4983230072969 + 3 ^ 40 * 2599971 * 2
def baseEnd_2599971 : Nat := 148337201194550259467273

theorem tailTrace_2599971 : CollatzResearch.WordTrace tailWord_2599971 prefixEnd_2599971 148337201194550259467273 := by
  unfold tailWord_2599971
  simp only [CollatzResearch.WordTrace]
  refine ⟨94828732863756581540103767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63219155242504387693402511 94828732863756581540103767)
  ·
    refine ⟨142243099295634872310155651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94828732863756581540103767 142243099295634872310155651)
    ·
      refine ⟨213364648943452308465233477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142243099295634872310155651 213364648943452308465233477)
      ·
        refine ⟨40005871676897307837231277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213364648943452308465233477 40005871676897307837231277)
        ·
          refine ⟨15002201878836490438961729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40005871676897307837231277 15002201878836490438961729)
          ·
            refine ⟨11251651409127367829221297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15002201878836490438961729 11251651409127367829221297)
            ·
              refine ⟨8438738556845525871915973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11251651409127367829221297 8438738556845525871915973)
              ·
                refine ⟨1582263479408536100984245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8438738556845525871915973 1582263479408536100984245)
                ·
                  refine ⟨148337201194550259467273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582263479408536100984245 148337201194550259467273)
                  ·
                    rfl

theorem cell23_2599971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 5].length) (baseStart_2599971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599971 prefixEnd_2599971 := by exact prefixLift 2599971
  have htrace : WordTrace (prefixWord ++ tailWord_2599971) baseStart_2599971 baseEnd_2599971 := by
    simpa [prefixWord, tailWord_2599971, baseEnd_2599971] using wordTrace_append hprefix tailTrace_2599971
  have hstable : (prefixWord ++ tailWord_2599971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599971).length < 2 ^ (prefixWord ++ tailWord_2599971).sum := by decide
  have hdescent : baseEnd_2599971 < baseStart_2599971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599982 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_2599982 : Nat := 118140960795 + 2599982 * 2 ^ 59
def prefixEnd_2599982 : Nat := 4983230072969 + 3 ^ 40 * 2599982 * 2
def baseEnd_2599982 : Nat := 1335040459038151792167907

theorem tailTrace_2599982 : CollatzResearch.WordTrace tailWord_2599982 prefixEnd_2599982 1335040459038151792167907 := by
  unfold tailWord_2599982
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853641758339591302344275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63219422711144486945836133 11853641758339591302344275)
  ·
    refine ⟨17780462637509386953516413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11853641758339591302344275 17780462637509386953516413)
    ·
      refine ⟨6667673489066020107568655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17780462637509386953516413 6667673489066020107568655)
      ·
        refine ⟨10001510233599030161352983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6667673489066020107568655 10001510233599030161352983)
        ·
          refine ⟨15002265350398545242029475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10001510233599030161352983 15002265350398545242029475)
          ·
            refine ⟨22503398025597817863044213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15002265350398545242029475 22503398025597817863044213)
            ·
              refine ⟨2109693564899795424660395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22503398025597817863044213 2109693564899795424660395)
              ·
                refine ⟨3164540347349693136990593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109693564899795424660395 3164540347349693136990593)
                ·
                  refine ⟨2373405260512269852742945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164540347349693136990593 2373405260512269852742945)
                  ·
                    refine ⟨1780053945384202389557209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373405260512269852742945 1780053945384202389557209)
                    ·
                      refine ⟨1335040459038151792167907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780053945384202389557209 1335040459038151792167907)
                      ·
                        rfl

theorem cell23_2599982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_2599982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2599982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2599982 prefixEnd_2599982 := by exact prefixLift 2599982
  have htrace : WordTrace (prefixWord ++ tailWord_2599982) baseStart_2599982 baseEnd_2599982 := by
    simpa [prefixWord, tailWord_2599982, baseEnd_2599982] using wordTrace_append hprefix tailTrace_2599982
  have hstable : (prefixWord ++ tailWord_2599982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599982).length < 2 ^ (prefixWord ++ tailWord_2599982).sum := by decide
  have hdescent : baseEnd_2599982 < baseStart_2599982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600021 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2600021 : Nat := 118140960795 + 2600021 * 2 ^ 59
def prefixEnd_2600021 : Nat := 4983230072969 + 3 ^ 40 * 2600021 * 2
def baseEnd_2600021 : Nat := 1335060484783677139580227

theorem tailTrace_2600021 : CollatzResearch.WordTrace tailWord_2600021 prefixEnd_2600021 1335060484783677139580227 := by
  unfold tailWord_2600021
  simp only [CollatzResearch.WordTrace]
  refine ⟨94830556513575440079423917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63220371009050293386282611 94830556513575440079423917)
  ·
    refine ⟨35561458692590790029783969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94830556513575440079423917 35561458692590790029783969)
    ·
      refine ⟨26671094019443092522337977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35561458692590790029783969 26671094019443092522337977)
      ·
        refine ⟨20003320514582319391753483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26671094019443092522337977 20003320514582319391753483)
        ·
          refine ⟨30004980771873479087630225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20003320514582319391753483 30004980771873479087630225)
          ·
            refine ⟨22503735578905109315722669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30004980771873479087630225 22503735578905109315722669)
            ·
              refine ⟨8438900842089415993396001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22503735578905109315722669 8438900842089415993396001)
              ·
                refine ⟨6329175631567061995047001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438900842089415993396001 6329175631567061995047001)
                ·
                  refine ⟨4746881723675296496285251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6329175631567061995047001 4746881723675296496285251)
                  ·
                    refine ⟨7120322585512944744427877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4746881723675296496285251 7120322585512944744427877)
                    ·
                      refine ⟨1335060484783677139580227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7120322585512944744427877 1335060484783677139580227)
                      ·
                        rfl

theorem cell23_2600021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2600021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600021 prefixEnd_2600021 := by exact prefixLift 2600021
  have htrace : WordTrace (prefixWord ++ tailWord_2600021) baseStart_2600021 baseEnd_2600021 := by
    simpa [prefixWord, tailWord_2600021, baseEnd_2600021] using wordTrace_append hprefix tailTrace_2600021
  have hstable : (prefixWord ++ tailWord_2600021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600021).length < 2 ^ (prefixWord ++ tailWord_2600021).sum := by decide
  have hdescent : baseEnd_2600021 < baseStart_2600021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600022 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2600022 : Nat := 118140960795 + 2600022 * 2 ^ 59
def prefixEnd_2600022 : Nat := 4983230072969 + 3 ^ 40 * 2600022 * 2
def baseEnd_2600022 : Nat := 148340110918259070629747

theorem tailTrace_2600022 : CollatzResearch.WordTrace tailWord_2600022 prefixEnd_2600022 148340110918259070629747 := by
  unfold tailWord_2600022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926912061660738578138145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63220395324381211500140213 5926912061660738578138145)
  ·
    refine ⟨4445184046245553933603609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5926912061660738578138145 4445184046245553933603609)
    ·
      refine ⟨3333888034684165450202707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4445184046245553933603609 3333888034684165450202707)
      ·
        refine ⟨5000832052026248175304061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333888034684165450202707 5000832052026248175304061)
        ·
          refine ⟨1875312019509843065739023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5000832052026248175304061 1875312019509843065739023)
          ·
            refine ⟨2812968029264764598608535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875312019509843065739023 2812968029264764598608535)
            ·
              refine ⟨4219452043897146897912803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812968029264764598608535 4219452043897146897912803)
              ·
                refine ⟨6329178065845720346869205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219452043897146897912803 6329178065845720346869205)
                ·
                  refine ⟨148340110918259070629747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6329178065845720346869205 148340110918259070629747)
                  ·
                    rfl

theorem cell23_2600022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2600022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600022 prefixEnd_2600022 := by exact prefixLift 2600022
  have htrace : WordTrace (prefixWord ++ tailWord_2600022) baseStart_2600022 baseEnd_2600022 := by
    simpa [prefixWord, tailWord_2600022, baseEnd_2600022] using wordTrace_append hprefix tailTrace_2600022
  have hstable : (prefixWord ++ tailWord_2600022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600022).length < 2 ^ (prefixWord ++ tailWord_2600022).sum := by decide
  have hdescent : baseEnd_2600022 < baseStart_2600022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600078 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_2600078 : Nat := 118140960795 + 2600078 * 2 ^ 59
def prefixEnd_2600078 : Nat := 4983230072969 + 3 ^ 40 * 2600078 * 2
def baseEnd_2600078 : Nat := 148343305908998157396385

theorem tailTrace_2600078 : CollatzResearch.WordTrace tailWord_2600078 prefixEnd_2600078 148343305908998157396385 := by
  unfold tailWord_2600078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11854079434296117351781111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63221756982912625876165925 11854079434296117351781111)
  ·
    refine ⟨17781119151444176027671667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11854079434296117351781111 17781119151444176027671667)
    ·
      refine ⟨26671678727166264041507501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17781119151444176027671667 26671678727166264041507501)
      ·
        refine ⟨10001879522687349015565313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26671678727166264041507501 10001879522687349015565313)
        ·
          refine ⟨7501409642015511761673985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10001879522687349015565313 7501409642015511761673985)
          ·
            refine ⟨5626057231511633821255489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7501409642015511761673985 5626057231511633821255489)
            ·
              refine ⟨4219542923633725365941617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5626057231511633821255489 4219542923633725365941617)
              ·
                refine ⟨3164657192725294024456213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219542923633725365941617 3164657192725294024456213)
                ·
                  refine ⟨148343305908998157396385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3164657192725294024456213 148343305908998157396385)
                  ·
                    rfl

theorem cell23_2600078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_2600078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600078 prefixEnd_2600078 := by exact prefixLift 2600078
  have htrace : WordTrace (prefixWord ++ tailWord_2600078) baseStart_2600078 baseEnd_2600078 := by
    simpa [prefixWord, tailWord_2600078, baseEnd_2600078] using wordTrace_append hprefix tailTrace_2600078
  have hstable : (prefixWord ++ tailWord_2600078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600078).length < 2 ^ (prefixWord ++ tailWord_2600078).sum := by decide
  have hdescent : baseEnd_2600078 < baseStart_2600078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600082 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2600082 : Nat := 118140960795 + 2600082 * 2 ^ 59
def prefixEnd_2600082 : Nat := 4983230072969 + 3 ^ 40 * 2600082 * 2
def baseEnd_2600082 : Nat := 445030602367867133639149

theorem tailTrace_2600082 : CollatzResearch.WordTrace tailWord_2600082 prefixEnd_2600082 445030602367867133639149 := by
  unfold tailWord_2600082
  simp only [CollatzResearch.WordTrace]
  refine ⟨23708195341588611874348625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63221854244236298331596333 23708195341588611874348625)
  ·
    refine ⟨17781146506191458905761469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23708195341588611874348625 17781146506191458905761469)
    ·
      refine ⟨6667929939821797089660551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17781146506191458905761469 6667929939821797089660551)
      ·
        refine ⟨10001894909732695634490827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6667929939821797089660551 10001894909732695634490827)
        ·
          refine ⟨15002842364599043451736241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10001894909732695634490827 15002842364599043451736241)
          ·
            refine ⟨11252131773449282588802181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15002842364599043451736241 11252131773449282588802181)
            ·
              refine ⟨2109774707521740485400409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11252131773449282588802181 2109774707521740485400409)
              ·
                refine ⟨1582331030641305364050307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109774707521740485400409 1582331030641305364050307)
                ·
                  refine ⟨2373496545961958046075461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582331030641305364050307 2373496545961958046075461)
                  ·
                    refine ⟨445030602367867133639149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2373496545961958046075461 445030602367867133639149)
                    ·
                      rfl

theorem cell23_2600082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2600082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600082 prefixEnd_2600082 := by exact prefixLift 2600082
  have htrace : WordTrace (prefixWord ++ tailWord_2600082) baseStart_2600082 baseEnd_2600082 := by
    simpa [prefixWord, tailWord_2600082, baseEnd_2600082] using wordTrace_append hprefix tailTrace_2600082
  have hstable : (prefixWord ++ tailWord_2600082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600082).length < 2 ^ (prefixWord ++ tailWord_2600082).sum := by decide
  have hdescent : baseEnd_2600082 < baseStart_2600082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600111 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_2600111 : Nat := 118140960795 + 2600111 * 2 ^ 59
def prefixEnd_2600111 : Nat := 4983230072969 + 3 ^ 40 * 2600111 * 2
def baseEnd_2600111 : Nat := 1335106698042581787454813

theorem tailTrace_2600111 : CollatzResearch.WordTrace tailWord_2600111 prefixEnd_2600111 1335106698042581787454813 := by
  unfold tailWord_2600111
  simp only [CollatzResearch.WordTrace]
  refine ⟨94833839083249385450200187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63222559388832923633466791 94833839083249385450200187)
  ·
    refine ⟨142250758624874078175300281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94833839083249385450200187 142250758624874078175300281)
    ·
      refine ⟨106688068968655558631475211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142250758624874078175300281 106688068968655558631475211)
      ·
        refine ⟨160032103452983337947212817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106688068968655558631475211 160032103452983337947212817)
        ·
          refine ⟨120024077589737503460409613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160032103452983337947212817 120024077589737503460409613)
          ·
            refine ⟨45009029096151563797653605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120024077589737503460409613 45009029096151563797653605)
            ·
              refine ⟨8439192955528418212060051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45009029096151563797653605 8439192955528418212060051)
              ·
                refine ⟨12658789433292627318090077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8439192955528418212060051 12658789433292627318090077)
                ·
                  refine ⟨4747046037484735244283779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12658789433292627318090077 4747046037484735244283779)
                  ·
                    refine ⟨7120569056227102866425669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4747046037484735244283779 7120569056227102866425669)
                    ·
                      refine ⟨1335106698042581787454813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7120569056227102866425669 1335106698042581787454813)
                      ·
                        rfl

theorem cell23_2600111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_2600111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600111 prefixEnd_2600111 := by exact prefixLift 2600111
  have htrace : WordTrace (prefixWord ++ tailWord_2600111) baseStart_2600111 baseEnd_2600111 := by
    simpa [prefixWord, tailWord_2600111, baseEnd_2600111] using wordTrace_append hprefix tailTrace_2600111
  have hstable : (prefixWord ++ tailWord_2600111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600111).length < 2 ^ (prefixWord ++ tailWord_2600111).sum := by decide
  have hdescent : baseEnd_2600111 < baseStart_2600111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600121 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_2600121 : Nat := 118140960795 + 2600121 * 2 ^ 59
def prefixEnd_2600121 : Nat := 4983230072969 + 3 ^ 40 * 2600121 * 2
def baseEnd_2600121 : Nat := 445037277616375582776589

theorem tailTrace_2600121 : CollatzResearch.WordTrace tailWord_2600121 prefixEnd_2600121 445037277616375582776589 := by
  unfold tailWord_2600121
  simp only [CollatzResearch.WordTrace]
  refine ⟨94834203813213157158064217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63222802542142104772042811 94834203813213157158064217)
  ·
    refine ⟨71125652859909867868548163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94834203813213157158064217 71125652859909867868548163)
    ·
      refine ⟨106688479289864801802822245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71125652859909867868548163 106688479289864801802822245)
      ·
        refine ⟨20004089866849650338029171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106688479289864801802822245 20004089866849650338029171)
        ·
          refine ⟨30006134800274475507043757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20004089866849650338029171 30006134800274475507043757)
          ·
            refine ⟨11252300550102928315141409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30006134800274475507043757 11252300550102928315141409)
            ·
              refine ⟨8439225412577196236356057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11252300550102928315141409 8439225412577196236356057)
              ·
                refine ⟨6329419059432897177267043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8439225412577196236356057 6329419059432897177267043)
                ·
                  refine ⟨9494128589149345765900565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329419059432897177267043 9494128589149345765900565)
                  ·
                    refine ⟨445037277616375582776589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9494128589149345765900565 445037277616375582776589)
                    ·
                      rfl

theorem cell23_2600121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_2600121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600121 prefixEnd_2600121 := by exact prefixLift 2600121
  have htrace : WordTrace (prefixWord ++ tailWord_2600121) baseStart_2600121 baseEnd_2600121 := by
    simpa [prefixWord, tailWord_2600121, baseEnd_2600121] using wordTrace_append hprefix tailTrace_2600121
  have hstable : (prefixWord ++ tailWord_2600121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600121).length < 2 ^ (prefixWord ++ tailWord_2600121).sum := by decide
  have hdescent : baseEnd_2600121 < baseStart_2600121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600131 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 3]
def baseStart_2600131 : Nat := 118140960795 + 2600131 * 2 ^ 59
def prefixEnd_2600131 : Nat := 4983230072969 + 3 ^ 40 * 2600131 * 2
def baseEnd_2600131 : Nat := 1335116967655671709204721

theorem tailTrace_2600131 : CollatzResearch.WordTrace tailWord_2600131 prefixEnd_2600131 1335116967655671709204721 := by
  unfold tailWord_2600131
  simp only [CollatzResearch.WordTrace]
  refine ⟨94834568543176928865928247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63223045695451285910618831 94834568543176928865928247)
  ·
    refine ⟨142251852814765393298892371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94834568543176928865928247 142251852814765393298892371)
    ·
      refine ⟨213377779222148089948338557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142251852814765393298892371 213377779222148089948338557)
      ·
        refine ⟨80016667208305533730626959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213377779222148089948338557 80016667208305533730626959)
        ·
          refine ⟨120025000812458300595940439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80016667208305533730626959 120025000812458300595940439)
          ·
            refine ⟨180037501218687450893910659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120025000812458300595940439 180037501218687450893910659)
            ·
              refine ⟨270056251828031176340865989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180037501218687450893910659 270056251828031176340865989)
              ·
                refine ⟨50635547217755845563912373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270056251828031176340865989 50635547217755845563912373)
                ·
                  refine ⟨4747082551664610521616785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50635547217755845563912373 4747082551664610521616785)
                  ·
                    refine ⟨3560311913748457891212589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4747082551664610521616785 3560311913748457891212589)
                    ·
                      refine ⟨1335116967655671709204721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560311913748457891212589 1335116967655671709204721)
                      ·
                        rfl

theorem cell23_2600131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_2600131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600131 prefixEnd_2600131 := by exact prefixLift 2600131
  have htrace : WordTrace (prefixWord ++ tailWord_2600131) baseStart_2600131 baseEnd_2600131 := by
    simpa [prefixWord, tailWord_2600131, baseEnd_2600131] using wordTrace_append hprefix tailTrace_2600131
  have hstable : (prefixWord ++ tailWord_2600131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600131).length < 2 ^ (prefixWord ++ tailWord_2600131).sum := by decide
  have hdescent : baseEnd_2600131 < baseStart_2600131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600138 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_2600138 : Nat := 118140960795 + 2600138 * 2 ^ 59
def prefixEnd_2600138 : Nat := 4983230072969 + 3 ^ 40 * 2600138 * 2
def baseEnd_2600138 : Nat := 445040187340084393939063

theorem tailTrace_2600138 : CollatzResearch.WordTrace tailWord_2600138 prefixEnd_2600138 445040187340084393939063 := by
  unfold tailWord_2600138
  simp only [CollatzResearch.WordTrace]
  refine ⟨23708705963537892265358267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63223215902767712707622045 23708705963537892265358267)
  ·
    refine ⟨35563058945306838398037401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23708705963537892265358267 35563058945306838398037401)
    ·
      refine ⟨26672294208980128798528051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35563058945306838398037401 26672294208980128798528051)
      ·
        refine ⟨40008441313470193197792077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26672294208980128798528051 40008441313470193197792077)
        ·
          refine ⟨15003165492551322449172029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40008441313470193197792077 15003165492551322449172029)
          ·
            refine ⟨5626187059706745918439511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15003165492551322449172029 5626187059706745918439511)
            ·
              refine ⟨8439280589560118877659267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626187059706745918439511 8439280589560118877659267)
              ·
                refine ⟨12658920884340178316488901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8439280589560118877659267 12658920884340178316488901)
                ·
                  refine ⟨2373547665813783434341669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12658920884340178316488901 2373547665813783434341669)
                  ·
                    refine ⟨445040187340084393939063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2373547665813783434341669 445040187340084393939063)
                    ·
                      rfl

theorem cell23_2600138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_2600138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600138 prefixEnd_2600138 := by exact prefixLift 2600138
  have htrace : WordTrace (prefixWord ++ tailWord_2600138) baseStart_2600138 baseEnd_2600138 := by
    simpa [prefixWord, tailWord_2600138, baseEnd_2600138] using wordTrace_append hprefix tailTrace_2600138
  have hstable : (prefixWord ++ tailWord_2600138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600138).length < 2 ^ (prefixWord ++ tailWord_2600138).sum := by decide
  have hdescent : baseEnd_2600138 < baseStart_2600138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600179 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 1, 2, 2]
def baseStart_2600179 : Nat := 118140960795 + 2600179 * 2 ^ 59
def prefixEnd_2600179 : Nat := 4983230072969 + 3 ^ 40 * 2600179 * 2
def baseEnd_2600179 : Nat := 1335141614727087521404501

theorem tailTrace_2600179 : CollatzResearch.WordTrace tailWord_2600179 prefixEnd_2600179 1335141614727087521404501 := by
  unfold tailWord_2600179
  simp only [CollatzResearch.WordTrace]
  refine ⟨94836319247003033063675591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63224212831335355375783727 94836319247003033063675591)
  ·
    refine ⟨142254478870504549595513387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94836319247003033063675591 142254478870504549595513387)
    ·
      refine ⟨213381718305756824393270081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142254478870504549595513387 213381718305756824393270081)
      ·
        refine ⟨160036288729317618294952561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213381718305756824393270081 160036288729317618294952561)
        ·
          refine ⟨120027216546988213721214421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160036288729317618294952561 120027216546988213721214421)
          ·
            refine ⟨2813137887820036259090963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 120027216546988213721214421 2813137887820036259090963)
            ·
              refine ⟨4219706831730054388636445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813137887820036259090963 4219706831730054388636445)
              ·
                refine ⟨1582390061898770395738667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4219706831730054388636445 1582390061898770395738667)
                ·
                  refine ⟨2373585092848155593608001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582390061898770395738667 2373585092848155593608001)
                  ·
                    refine ⟨1780188819636116695206001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373585092848155593608001 1780188819636116695206001)
                    ·
                      refine ⟨1335141614727087521404501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780188819636116695206001 1335141614727087521404501)
                      ·
                        rfl

theorem cell23_2600179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 2, 2].length) (baseStart_2600179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600179 prefixEnd_2600179 := by exact prefixLift 2600179
  have htrace : WordTrace (prefixWord ++ tailWord_2600179) baseStart_2600179 baseEnd_2600179 := by
    simpa [prefixWord, tailWord_2600179, baseEnd_2600179] using wordTrace_append hprefix tailTrace_2600179
  have hstable : (prefixWord ++ tailWord_2600179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600179).length < 2 ^ (prefixWord ++ tailWord_2600179).sum := by decide
  have hdescent : baseEnd_2600179 < baseStart_2600179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600196 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2600196 : Nat := 118140960795 + 2600196 * 2 ^ 59
def prefixEnd_2600196 : Nat := 4983230072969 + 3 ^ 40 * 2600196 * 2
def baseEnd_2600196 : Nat := 1335150343898213954891923

theorem tailTrace_2600196 : CollatzResearch.WordTrace tailWord_2600196 prefixEnd_2600196 1335150343898213954891923 := by
  unfold tailWord_2600196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47418469643970722483522221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63224626191960963311362961 47418469643970722483522221)
  ·
    refine ⟨17781926116489020931320833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47418469643970722483522221 17781926116489020931320833)
    ·
      refine ⟨13336444587366765698490625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17781926116489020931320833 13336444587366765698490625)
      ·
        refine ⟨10002333440525074273867969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13336444587366765698490625 10002333440525074273867969)
        ·
          refine ⟨7501750080393805705400977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10002333440525074273867969 7501750080393805705400977)
          ·
            refine ⟨5626312560295354279050733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7501750080393805705400977 5626312560295354279050733)
            ·
              refine ⟨2109867210110757854644025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5626312560295354279050733 2109867210110757854644025)
              ·
                refine ⟨1582400407583068390983019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109867210110757854644025 1582400407583068390983019)
                ·
                  refine ⟨2373600611374602586474529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582400407583068390983019 2373600611374602586474529)
                  ·
                    refine ⟨1780200458530951939855897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373600611374602586474529 1780200458530951939855897)
                    ·
                      refine ⟨1335150343898213954891923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780200458530951939855897 1335150343898213954891923)
                      ·
                        rfl

theorem cell23_2600196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2600196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600196 prefixEnd_2600196 := by exact prefixLift 2600196
  have htrace : WordTrace (prefixWord ++ tailWord_2600196) baseStart_2600196 baseEnd_2600196 := by
    simpa [prefixWord, tailWord_2600196, baseEnd_2600196] using wordTrace_append hprefix tailTrace_2600196
  have hstable : (prefixWord ++ tailWord_2600196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600196).length < 2 ^ (prefixWord ++ tailWord_2600196).sum := by decide
  have hdescent : baseEnd_2600196 < baseStart_2600196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600201 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_2600201 : Nat := 118140960795 + 2600201 * 2 ^ 59
def prefixEnd_2600201 : Nat := 4983230072969 + 3 ^ 40 * 2600201 * 2
def baseEnd_2600201 : Nat := 1335152911301486435329399

theorem tailTrace_2600201 : CollatzResearch.WordTrace tailWord_2600201 prefixEnd_2600201 1335152911301486435329399 := by
  unfold tailWord_2600201
  simp only [CollatzResearch.WordTrace]
  refine ⟨94837121652923330820976457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63224747768615553880650971 94837121652923330820976457)
  ·
    refine ⟨71127841239692498115732343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94837121652923330820976457 71127841239692498115732343)
    ·
      refine ⟨106691761859538747173598515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71127841239692498115732343 106691761859538747173598515)
      ·
        refine ⟨160037642789308120760397773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106691761859538747173598515 160037642789308120760397773)
        ·
          refine ⟨60014116045990545285149165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160037642789308120760397773 60014116045990545285149165)
          ·
            refine ⟨22505293517246454481930937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60014116045990545285149165 22505293517246454481930937)
            ·
              refine ⟨16878970137934840861448203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22505293517246454481930937 16878970137934840861448203)
              ·
                refine ⟨25318455206902261292172305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16878970137934840861448203 25318455206902261292172305)
                ·
                  refine ⟨18988841405176695969129229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25318455206902261292172305 18988841405176695969129229)
                  ·
                    refine ⟨7120815526941260988423461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18988841405176695969129229 7120815526941260988423461)
                    ·
                      refine ⟨1335152911301486435329399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7120815526941260988423461 1335152911301486435329399)
                      ·
                        rfl

theorem cell23_2600201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_2600201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600201 prefixEnd_2600201 := by exact prefixLift 2600201
  have htrace : WordTrace (prefixWord ++ tailWord_2600201) baseStart_2600201 baseEnd_2600201 := by
    simpa [prefixWord, tailWord_2600201, baseEnd_2600201] using wordTrace_append hprefix tailTrace_2600201
  have hstable : (prefixWord ++ tailWord_2600201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600201).length < 2 ^ (prefixWord ++ tailWord_2600201).sum := by decide
  have hdescent : baseEnd_2600201 < baseStart_2600201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600246 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2600246 : Nat := 118140960795 + 2600246 * 2 ^ 59
def prefixEnd_2600246 : Nat := 4983230072969 + 3 ^ 40 * 2600246 * 2
def baseEnd_2600246 : Nat := 1335176017930938759266693

theorem tailTrace_2600246 : CollatzResearch.WordTrace tailWord_2600246 prefixEnd_2600246 1335176017930938759266693 := by
  unfold tailWord_2600246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5927422683610018969147787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63225841958506869004243061 5927422683610018969147787)
  ·
    refine ⟨8891134025415028453721681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5927422683610018969147787 8891134025415028453721681)
    ·
      refine ⟨6668350519061271340291261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8891134025415028453721681 6668350519061271340291261)
      ·
        refine ⟨2500631444647976752609223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6668350519061271340291261 2500631444647976752609223)
        ·
          refine ⟨3750947166971965128913835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500631444647976752609223 3750947166971965128913835)
          ·
            refine ⟨5626420750457947693370753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750947166971965128913835 5626420750457947693370753)
            ·
              refine ⟨4219815562843460770028065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5626420750457947693370753 4219815562843460770028065)
              ·
                refine ⟨3164861672132595577521049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219815562843460770028065 3164861672132595577521049)
                ·
                  refine ⟨2373646254099446683140787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164861672132595577521049 2373646254099446683140787)
                  ·
                    refine ⟨3560469381149170024711181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2373646254099446683140787 3560469381149170024711181)
                    ·
                      refine ⟨1335176017930938759266693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560469381149170024711181 1335176017930938759266693)
                      ·
                        rfl

theorem cell23_2600246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2600246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600246 prefixEnd_2600246 := by exact prefixLift 2600246
  have htrace : WordTrace (prefixWord ++ tailWord_2600246) baseStart_2600246 baseEnd_2600246 := by
    simpa [prefixWord, tailWord_2600246, baseEnd_2600246] using wordTrace_append hprefix tailTrace_2600246
  have hstable : (prefixWord ++ tailWord_2600246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600246).length < 2 ^ (prefixWord ++ tailWord_2600246).sum := by decide
  have hdescent : baseEnd_2600246 < baseStart_2600246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600252 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_2600252 : Nat := 118140960795 + 2600252 * 2 ^ 59
def prefixEnd_2600252 : Nat := 4983230072969 + 3 ^ 40 * 2600252 * 2
def baseEnd_2600252 : Nat := 1335179098814865735791665

theorem tailTrace_2600252 : CollatzResearch.WordTrace tailWord_2600252 prefixEnd_2600252 1335179098814865735791665 := by
  unfold tailWord_2600252
  simp only [CollatzResearch.WordTrace]
  refine ⟨47419490887869283265541505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63225987850492377687388673 47419490887869283265541505)
  ·
    refine ⟨35564618165901962449156129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47419490887869283265541505 35564618165901962449156129)
    ·
      refine ⟨26673463624426471836867097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35564618165901962449156129 26673463624426471836867097)
      ·
        refine ⟨20005097718319853877650323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26673463624426471836867097 20005097718319853877650323)
        ·
          refine ⟨30007646577479780816475485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20005097718319853877650323 30007646577479780816475485)
          ·
            refine ⟨11252867466554917806178307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30007646577479780816475485 11252867466554917806178307)
            ·
              refine ⟨16879301199832376709267461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252867466554917806178307 16879301199832376709267461)
              ·
                refine ⟨3164868974968570632987649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16879301199832376709267461 3164868974968570632987649)
                ·
                  refine ⟨2373651731226427974740737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164868974968570632987649 2373651731226427974740737)
                  ·
                    refine ⟨1780238798419820981055553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373651731226427974740737 1780238798419820981055553)
                    ·
                      refine ⟨1335179098814865735791665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780238798419820981055553 1335179098814865735791665)
                      ·
                        rfl

theorem cell23_2600252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_2600252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600252 prefixEnd_2600252 := by exact prefixLift 2600252
  have htrace : WordTrace (prefixWord ++ tailWord_2600252) baseStart_2600252 baseEnd_2600252 := by
    simpa [prefixWord, tailWord_2600252, baseEnd_2600252] using wordTrace_append hprefix tailTrace_2600252
  have hstable : (prefixWord ++ tailWord_2600252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600252).length < 2 ^ (prefixWord ++ tailWord_2600252).sum := by decide
  have hdescent : baseEnd_2600252 < baseStart_2600252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600268 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2600268 : Nat := 118140960795 + 2600268 * 2 ^ 59
def prefixEnd_2600268 : Nat := 4983230072969 + 3 ^ 40 * 2600268 * 2
def baseEnd_2600268 : Nat := 1335187314505337673191591

theorem tailTrace_2600268 : CollatzResearch.WordTrace tailWord_2600268 prefixEnd_2600268 1335187314505337673191591 := by
  unfold tailWord_2600268
  simp only [CollatzResearch.WordTrace]
  refine ⟨47419782671840300631832729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63226376895787067509110305 47419782671840300631832729)
  ·
    refine ⟨35564837003880225473874547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47419782671840300631832729 35564837003880225473874547)
    ·
      refine ⟨53347255505820338210811821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35564837003880225473874547 53347255505820338210811821)
      ·
        refine ⟨20005220814682626829054433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53347255505820338210811821 20005220814682626829054433)
        ·
          refine ⟨15003915611011970121790825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20005220814682626829054433 15003915611011970121790825)
          ·
            refine ⟨11252936708258977591343119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15003915611011970121790825 11252936708258977591343119)
            ·
              refine ⟨16879405062388466387014679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252936708258977591343119 16879405062388466387014679)
              ·
                refine ⟨25319107593582699580522019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16879405062388466387014679 25319107593582699580522019)
                ·
                  refine ⟨37978661390374049370783029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25319107593582699580522019 37978661390374049370783029)
                  ·
                    refine ⟨3560499505347567128510909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37978661390374049370783029 3560499505347567128510909)
                    ·
                      refine ⟨1335187314505337673191591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560499505347567128510909 1335187314505337673191591)
                      ·
                        rfl

theorem cell23_2600268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2600268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600268 prefixEnd_2600268 := by exact prefixLift 2600268
  have htrace : WordTrace (prefixWord ++ tailWord_2600268) baseStart_2600268 baseEnd_2600268 := by
    simpa [prefixWord, tailWord_2600268, baseEnd_2600268] using wordTrace_append hprefix tailTrace_2600268
  have hstable : (prefixWord ++ tailWord_2600268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600268).length < 2 ^ (prefixWord ++ tailWord_2600268).sum := by decide
  have hdescent : baseEnd_2600268 < baseStart_2600268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600281 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_2600281 : Nat := 118140960795 + 2600281 * 2 ^ 59
def prefixEnd_2600281 : Nat := 4983230072969 + 3 ^ 40 * 2600281 * 2
def baseEnd_2600281 : Nat := 1335193989753846122329031

theorem tailTrace_2600281 : CollatzResearch.WordTrace tailWord_2600281 prefixEnd_2600281 1335193989753846122329031 := by
  unfold tailWord_2600281
  simp only [CollatzResearch.WordTrace]
  refine ⟨94840039492633504483888697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63226692995089002989259131 94840039492633504483888697)
  ·
    refine ⟨71130029619475128362916523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94840039492633504483888697 71130029619475128362916523)
    ·
      refine ⟨106695044429212692544374785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71130029619475128362916523 106695044429212692544374785)
      ·
        refine ⟨80021283321909519408281089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106695044429212692544374785 80021283321909519408281089)
        ·
          refine ⟨60015962491432139556210817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80021283321909519408281089 60015962491432139556210817)
          ·
            refine ⟨45011971868574104667158113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60015962491432139556210817 45011971868574104667158113)
            ·
              refine ⟨33758978901430578500368585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45011971868574104667158113 33758978901430578500368585)
              ·
                refine ⟨25319234176072933875276439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33758978901430578500368585 25319234176072933875276439)
                ·
                  refine ⟨37978851264109400812914659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25319234176072933875276439 37978851264109400812914659)
                  ·
                    refine ⟨56968276896164101219371989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37978851264109400812914659 56968276896164101219371989)
                    ·
                      refine ⟨1335193989753846122329031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56968276896164101219371989 1335193989753846122329031)
                      ·
                        rfl

theorem cell23_2600281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_2600281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600281 prefixEnd_2600281 := by exact prefixLift 2600281
  have htrace : WordTrace (prefixWord ++ tailWord_2600281) baseStart_2600281 baseEnd_2600281 := by
    simpa [prefixWord, tailWord_2600281, baseEnd_2600281] using wordTrace_append hprefix tailTrace_2600281
  have hstable : (prefixWord ++ tailWord_2600281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600281).length < 2 ^ (prefixWord ++ tailWord_2600281).sum := by decide
  have hdescent : baseEnd_2600281 < baseStart_2600281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600288 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_2600288 : Nat := 118140960795 + 2600288 * 2 ^ 59
def prefixEnd_2600288 : Nat := 4983230072969 + 3 ^ 40 * 2600288 * 2
def baseEnd_2600288 : Nat := 445065861372809198313833

theorem tailTrace_2600288 : CollatzResearch.WordTrace tailWord_2600288 prefixEnd_2600288 445065861372809198313833 := by
  unfold tailWord_2600288
  simp only [CollatzResearch.WordTrace]
  refine ⟨47420147401804072339696759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63226863202405429786262345 47420147401804072339696759)
  ·
    refine ⟨71130221102706108509545139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47420147401804072339696759 71130221102706108509545139)
    ·
      refine ⟨106695331654059162764317709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71130221102706108509545139 106695331654059162764317709)
      ·
        refine ⟨40010749370272186036619141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106695331654059162764317709 40010749370272186036619141)
        ·
          refine ⟨7502015506926034881866089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40010749370272186036619141 7502015506926034881866089)
          ·
            refine ⟨5626511630194526161399567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7502015506926034881866089 5626511630194526161399567)
            ·
              refine ⟨8439767445291789242099351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626511630194526161399567 8439767445291789242099351)
              ·
                refine ⟨12659651167937683863149027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8439767445291789242099351 12659651167937683863149027)
                ·
                  refine ⟨18989476751906525794723541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12659651167937683863149027 18989476751906525794723541)
                  ·
                    refine ⟨445065861372809198313833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18989476751906525794723541 445065861372809198313833)
                    ·
                      rfl

theorem cell23_2600288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_2600288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600288 prefixEnd_2600288 := by exact prefixLift 2600288
  have htrace : WordTrace (prefixWord ++ tailWord_2600288) baseStart_2600288 baseEnd_2600288 := by
    simpa [prefixWord, tailWord_2600288, baseEnd_2600288] using wordTrace_append hprefix tailTrace_2600288
  have hstable : (prefixWord ++ tailWord_2600288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600288).length < 2 ^ (prefixWord ++ tailWord_2600288).sum := by decide
  have hdescent : baseEnd_2600288 < baseStart_2600288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600325 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 2, 4, 2]
def baseStart_2600325 : Nat := 118140960795 + 2600325 * 2 ^ 59
def prefixEnd_2600325 : Nat := 4983230072969 + 3 ^ 40 * 2600325 * 2
def baseEnd_2600325 : Nat := 1335216582902643950178829

theorem tailTrace_2600325 : CollatzResearch.WordTrace tailWord_2600325 prefixEnd_2600325 1335216582902643950178829 := by
  unfold tailWord_2600325
  simp only [CollatzResearch.WordTrace]
  refine ⟨94841644304474099998490429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63227762869649399998993619 94841644304474099998490429)
  ·
    refine ⟨35565616614177787499433911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94841644304474099998490429 35565616614177787499433911)
    ·
      refine ⟨53348424921266681249150867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35565616614177787499433911 53348424921266681249150867)
      ·
        refine ⟨80022637381900021873726301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53348424921266681249150867 80022637381900021873726301)
        ·
          refine ⟨30008489018212508202647363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80022637381900021873726301 30008489018212508202647363)
          ·
            refine ⟨45012733527318762303971045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30008489018212508202647363 45012733527318762303971045)
            ·
              refine ⟨8439887536372267931994571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45012733527318762303971045 8439887536372267931994571)
              ·
                refine ⟨12659831304558401897991857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8439887536372267931994571 12659831304558401897991857)
                ·
                  refine ⟨9494873478418801423493893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12659831304558401897991857 9494873478418801423493893)
                  ·
                    refine ⟨1780288777203525266905105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9494873478418801423493893 1780288777203525266905105)
                    ·
                      refine ⟨1335216582902643950178829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780288777203525266905105 1335216582902643950178829)
                      ·
                        rfl

theorem cell23_2600325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_2600325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600325 prefixEnd_2600325 := by exact prefixLift 2600325
  have htrace : WordTrace (prefixWord ++ tailWord_2600325) baseStart_2600325 baseEnd_2600325 := by
    simpa [prefixWord, tailWord_2600325, baseEnd_2600325] using wordTrace_append hprefix tailTrace_2600325
  have hstable : (prefixWord ++ tailWord_2600325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600325).length < 2 ^ (prefixWord ++ tailWord_2600325).sum := by decide
  have hdescent : baseEnd_2600325 < baseStart_2600325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600365 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2600365 : Nat := 118140960795 + 2600365 * 2 ^ 59
def prefixEnd_2600365 : Nat := 4983230072969 + 3 ^ 40 * 2600365 * 2
def baseEnd_2600365 : Nat := 148359680236535977075405

theorem tailTrace_2600365 : CollatzResearch.WordTrace tailWord_2600365 prefixEnd_2600365 148359680236535977075405 := by
  unfold tailWord_2600365
  simp only [CollatzResearch.WordTrace]
  refine ⟨94843103224329186829946549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63228735482886124553297699 94843103224329186829946549)
  ·
    refine ⟨8891540927280861265307489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94843103224329186829946549 8891540927280861265307489)
    ·
      refine ⟨6668655695460645948980617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8891540927280861265307489 6668655695460645948980617)
      ·
        refine ⟨5001491771595484461735463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6668655695460645948980617 5001491771595484461735463)
        ·
          refine ⟨7502237657393226692603195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5001491771595484461735463 7502237657393226692603195)
          ·
            refine ⟨11253356486089840038904793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502237657393226692603195 11253356486089840038904793)
            ·
              refine ⟨8440017364567380029178595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11253356486089840038904793 8440017364567380029178595)
              ·
                refine ⟨12660026046851070043767893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8440017364567380029178595 12660026046851070043767893)
                ·
                  refine ⟨148359680236535977075405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12660026046851070043767893 148359680236535977075405)
                  ·
                    rfl

theorem cell23_2600365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2600365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600365 prefixEnd_2600365 := by exact prefixLift 2600365
  have htrace : WordTrace (prefixWord ++ tailWord_2600365) baseStart_2600365 baseEnd_2600365 := by
    simpa [prefixWord, tailWord_2600365, baseEnd_2600365] using wordTrace_append hprefix tailTrace_2600365
  have hstable : (prefixWord ++ tailWord_2600365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600365).length < 2 ^ (prefixWord ++ tailWord_2600365).sum := by decide
  have hdescent : baseEnd_2600365 < baseStart_2600365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600369 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 1, 4]
def baseStart_2600369 : Nat := 118140960795 + 2600369 * 2 ^ 59
def prefixEnd_2600369 : Nat := 4983230072969 + 3 ^ 40 * 2600369 * 2
def baseEnd_2600369 : Nat := 445079725350480592676209

theorem tailTrace_2600369 : CollatzResearch.WordTrace tailWord_2600369 prefixEnd_2600369 445079725350480592676209 := by
  unfold tailWord_2600369
  simp only [CollatzResearch.WordTrace]
  refine ⟨94843249116314695513092161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63228832744209797008728107 94843249116314695513092161)
  ·
    refine ⟨71132436837236021634819121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94843249116314695513092161 71132436837236021634819121)
    ·
      refine ⟨53349327627927016226114341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71132436837236021634819121 53349327627927016226114341)
      ·
        refine ⟨10002998930236315542396439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53349327627927016226114341 10002998930236315542396439)
        ·
          refine ⟨15004498395354473313594659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10002998930236315542396439 15004498395354473313594659)
          ·
            refine ⟨22506747593031709970391989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15004498395354473313594659 22506747593031709970391989)
            ·
              refine ⟨2110007586846722809724249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22506747593031709970391989 2110007586846722809724249)
              ·
                refine ⟨1582505690135042107293187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110007586846722809724249 1582505690135042107293187)
                ·
                  refine ⟨2373758535202563160939781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582505690135042107293187 2373758535202563160939781)
                  ·
                    refine ⟨445079725350480592676209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2373758535202563160939781 445079725350480592676209)
                    ·
                      rfl

theorem cell23_2600369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_2600369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600369 prefixEnd_2600369 := by exact prefixLift 2600369
  have htrace : WordTrace (prefixWord ++ tailWord_2600369) baseStart_2600369 baseEnd_2600369 := by
    simpa [prefixWord, tailWord_2600369, baseEnd_2600369] using wordTrace_append hprefix tailTrace_2600369
  have hstable : (prefixWord ++ tailWord_2600369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600369).length < 2 ^ (prefixWord ++ tailWord_2600369).sum := by decide
  have hdescent : baseEnd_2600369 < baseStart_2600369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600395 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 1, 5]
def baseStart_2600395 : Nat := 118140960795 + 2600395 * 2 ^ 59
def prefixEnd_2600395 : Nat := 4983230072969 + 3 ^ 40 * 2600395 * 2
def baseEnd_2600395 : Nat := 445084175516152892101169

theorem tailTrace_2600395 : CollatzResearch.WordTrace tailWord_2600395 prefixEnd_2600395 445084175516152892101169 := by
  unfold tailWord_2600395
  simp only [CollatzResearch.WordTrace]
  refine ⟨94844197414220501953538639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63229464942813667969025759 94844197414220501953538639)
  ·
    refine ⟨142266296121330752930307959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94844197414220501953538639 142266296121330752930307959)
    ·
      refine ⟨213399444181996129395461939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142266296121330752930307959 213399444181996129395461939)
      ·
        refine ⟨320099166272994194093192909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213399444181996129395461939 320099166272994194093192909)
        ·
          refine ⟨120037187352372822784947341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320099166272994194093192909 120037187352372822784947341)
          ·
            refine ⟨45013945257139808544355253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120037187352372822784947341 45013945257139808544355253)
            ·
              refine ⟨4220057367856857051033305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45013945257139808544355253 4220057367856857051033305)
              ·
                refine ⟨3165043025892642788274979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220057367856857051033305 3165043025892642788274979)
                ·
                  refine ⟨4747564538838964182412469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165043025892642788274979 4747564538838964182412469)
                  ·
                    refine ⟨445084175516152892101169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4747564538838964182412469 445084175516152892101169)
                    ·
                      rfl

theorem cell23_2600395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 5].length) (baseStart_2600395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600395 prefixEnd_2600395 := by exact prefixLift 2600395
  have htrace : WordTrace (prefixWord ++ tailWord_2600395) baseStart_2600395 baseEnd_2600395 := by
    simpa [prefixWord, tailWord_2600395, baseEnd_2600395] using wordTrace_append hprefix tailTrace_2600395
  have hstable : (prefixWord ++ tailWord_2600395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600395).length < 2 ^ (prefixWord ++ tailWord_2600395).sum := by decide
  have hdescent : baseEnd_2600395 < baseStart_2600395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600408 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_2600408 : Nat := 118140960795 + 2600408 * 2 ^ 59
def prefixEnd_2600408 : Nat := 4983230072969 + 3 ^ 40 * 2600408 * 2
def baseEnd_2600408 : Nat := 445086400598989041813649

theorem tailTrace_2600408 : CollatzResearch.WordTrace tailWord_2600408 prefixEnd_2600408 445086400598989041813649 := by
  unfold tailWord_2600408
  simp only [CollatzResearch.WordTrace]
  refine ⟨47422335781586702586880939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63229781042115603449174585 47422335781586702586880939)
  ·
    refine ⟨71133503672380053880321409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47422335781586702586880939 71133503672380053880321409)
    ·
      refine ⟨53350127754285040410241057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71133503672380053880321409 53350127754285040410241057)
      ·
        refine ⟨40012595815713780307680793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53350127754285040410241057 40012595815713780307680793)
        ·
          refine ⟨30009446861785335230760595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40012595815713780307680793 30009446861785335230760595)
          ·
            refine ⟨45014170292678002846140893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30009446861785335230760595 45014170292678002846140893)
            ·
              refine ⟨16880313859754251067302835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45014170292678002846140893 16880313859754251067302835)
              ·
                refine ⟨25320470789631376600954253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16880313859754251067302835 25320470789631376600954253)
                ·
                  refine ⟨9495176546111766225357845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25320470789631376600954253 9495176546111766225357845)
                  ·
                    refine ⟨445086400598989041813649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9495176546111766225357845 445086400598989041813649)
                    ·
                      rfl

theorem cell23_2600408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_2600408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600408 prefixEnd_2600408 := by exact prefixLift 2600408
  have htrace : WordTrace (prefixWord ++ tailWord_2600408) baseStart_2600408 baseEnd_2600408 := by
    simpa [prefixWord, tailWord_2600408, baseEnd_2600408] using wordTrace_append hprefix tailTrace_2600408
  have hstable : (prefixWord ++ tailWord_2600408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600408).length < 2 ^ (prefixWord ++ tailWord_2600408).sum := by decide
  have hdescent : baseEnd_2600408 < baseStart_2600408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600426 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_2600426 : Nat := 118140960795 + 2600426 * 2 ^ 59
def prefixEnd_2600426 : Nat := 4983230072969 + 3 ^ 40 * 2600426 * 2
def baseEnd_2600426 : Nat := 1335268444448748055015865

theorem tailTrace_2600426 : CollatzResearch.WordTrace tailWord_2600426 prefixEnd_2600426 1335268444448748055015865 := by
  unfold tailWord_2600426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23711332019277048561979283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63230218718072129498611421 23711332019277048561979283)
  ·
    refine ⟨35566998028915572842968925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23711332019277048561979283 35566998028915572842968925)
    ·
      refine ⟨13337624260843339816113347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35566998028915572842968925 13337624260843339816113347)
      ·
        refine ⟨20006436391265009724170021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13337624260843339816113347 20006436391265009724170021)
        ·
          refine ⟨3751206823362189323281879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20006436391265009724170021 3751206823362189323281879)
          ·
            refine ⟨5626810235043283984922819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751206823362189323281879 5626810235043283984922819)
            ·
              refine ⟨8440215352564925977384229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626810235043283984922819 8440215352564925977384229)
              ·
                refine ⟨1582540378605923620759543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8440215352564925977384229 1582540378605923620759543)
                ·
                  refine ⟨2373810567908885431139315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582540378605923620759543 2373810567908885431139315)
                  ·
                    refine ⟨3560715851863328146708973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2373810567908885431139315 3560715851863328146708973)
                    ·
                      refine ⟨1335268444448748055015865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560715851863328146708973 1335268444448748055015865)
                      ·
                        rfl

theorem cell23_2600426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_2600426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600426 prefixEnd_2600426 := by exact prefixLift 2600426
  have htrace : WordTrace (prefixWord ++ tailWord_2600426) baseStart_2600426 baseEnd_2600426 := by
    simpa [prefixWord, tailWord_2600426, baseEnd_2600426] using wordTrace_append hprefix tailTrace_2600426
  have hstable : (prefixWord ++ tailWord_2600426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600426).length < 2 ^ (prefixWord ++ tailWord_2600426).sum := by decide
  have hdescent : baseEnd_2600426 < baseStart_2600426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600428 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2600428 : Nat := 118140960795 + 2600428 * 2 ^ 59
def prefixEnd_2600428 : Nat := 4983230072969 + 3 ^ 40 * 2600428 * 2
def baseEnd_2600428 : Nat := 1335269471410057047190855

theorem tailTrace_2600428 : CollatzResearch.WordTrace tailWord_2600428 prefixEnd_2600428 1335269471410057047190855 := by
  unfold tailWord_2600428
  simp only [CollatzResearch.WordTrace]
  refine ⟨47422700511550474294744969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63230267348733965726326625 47422700511550474294744969)
  ·
    refine ⟨35567025383662855721058727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47422700511550474294744969 35567025383662855721058727)
    ·
      refine ⟨53350538075494283581588091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35567025383662855721058727 53350538075494283581588091)
      ·
        refine ⟨80025807113241425372382137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53350538075494283581588091 80025807113241425372382137)
        ·
          refine ⟨60019355334931069029286603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80025807113241425372382137 60019355334931069029286603)
          ·
            refine ⟨90029033002396603543929905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60019355334931069029286603 90029033002396603543929905)
            ·
              refine ⟨67521774751797452657947429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90029033002396603543929905 67521774751797452657947429)
              ·
                refine ⟨12660332765962022373365143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67521774751797452657947429 12660332765962022373365143)
                ·
                  refine ⟨18990499148943033560047715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12660332765962022373365143 18990499148943033560047715)
                  ·
                    refine ⟨28485748723414550340071573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18990499148943033560047715 28485748723414550340071573)
                    ·
                      refine ⟨1335269471410057047190855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28485748723414550340071573 1335269471410057047190855)
                      ·
                        rfl

theorem cell23_2600428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2600428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600428 prefixEnd_2600428 := by exact prefixLift 2600428
  have htrace : WordTrace (prefixWord ++ tailWord_2600428) baseStart_2600428 baseEnd_2600428 := by
    simpa [prefixWord, tailWord_2600428, baseEnd_2600428] using wordTrace_append hprefix tailTrace_2600428
  have hstable : (prefixWord ++ tailWord_2600428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600428).length < 2 ^ (prefixWord ++ tailWord_2600428).sum := by decide
  have hdescent : baseEnd_2600428 < baseStart_2600428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600445 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_2600445 : Nat := 118140960795 + 2600445 * 2 ^ 59
def prefixEnd_2600445 : Nat := 4983230072969 + 3 ^ 40 * 2600445 * 2
def baseEnd_2600445 : Nat := 1335278200581183480678277

theorem tailTrace_2600445 : CollatzResearch.WordTrace tailWord_2600445 prefixEnd_2600445 1335278200581183480678277 := by
  unfold tailWord_2600445
  simp only [CollatzResearch.WordTrace]
  refine ⟨94846021064039360492858789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63230680709359573661905859 94846021064039360492858789)
  ·
    refine ⟨17783628949507380092411023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94846021064039360492858789 17783628949507380092411023)
    ·
      refine ⟨26675443424261070138616535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17783628949507380092411023 26675443424261070138616535)
      ·
        refine ⟨40013165136391605207924803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26675443424261070138616535 40013165136391605207924803)
        ·
          refine ⟨60019747704587407811887205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40013165136391605207924803 60019747704587407811887205)
          ·
            refine ⟨11253702694610138964728851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60019747704587407811887205 11253702694610138964728851)
            ·
              refine ⟨16880554041915208447093277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11253702694610138964728851 16880554041915208447093277)
              ·
                refine ⟨6330207765718203167659979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16880554041915208447093277 6330207765718203167659979)
                ·
                  refine ⟨9495311648577304751489969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330207765718203167659979 9495311648577304751489969)
                  ·
                    refine ⟨7121483736432978563617477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9495311648577304751489969 7121483736432978563617477)
                    ·
                      refine ⟨1335278200581183480678277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7121483736432978563617477 1335278200581183480678277)
                      ·
                        rfl

theorem cell23_2600445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_2600445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600445 prefixEnd_2600445 := by exact prefixLift 2600445
  have htrace : WordTrace (prefixWord ++ tailWord_2600445) baseStart_2600445 baseEnd_2600445 := by
    simpa [prefixWord, tailWord_2600445, baseEnd_2600445] using wordTrace_append hprefix tailTrace_2600445
  have hstable : (prefixWord ++ tailWord_2600445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600445).length < 2 ^ (prefixWord ++ tailWord_2600445).sum := by decide
  have hdescent : baseEnd_2600445 < baseStart_2600445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600465 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_2600465 : Nat := 118140960795 + 2600465 * 2 ^ 59
def prefixEnd_2600465 : Nat := 4983230072969 + 3 ^ 40 * 2600465 * 2
def baseEnd_2600465 : Nat := 1335288470194273402428185

theorem tailTrace_2600465 : CollatzResearch.WordTrace tailWord_2600465 prefixEnd_2600465 1335288470194273402428185 := by
  unfold tailWord_2600465
  simp only [CollatzResearch.WordTrace]
  refine ⟨94846750523966903908586849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63231167015977935939057899 94846750523966903908586849)
  ·
    refine ⟨71135062892975177931440137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94846750523966903908586849 71135062892975177931440137)
    ·
      refine ⟨53351297169731383448580103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71135062892975177931440137 53351297169731383448580103)
      ·
        refine ⟨80026945754597075172870155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53351297169731383448580103 80026945754597075172870155)
        ·
          refine ⟨120040418631895612759305233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80026945754597075172870155 120040418631895612759305233)
          ·
            refine ⟨90030313973921709569478925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120040418631895612759305233 90030313973921709569478925)
            ·
              refine ⟨33761367740220641088554597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90030313973921709569478925 33761367740220641088554597)
              ·
                refine ⟨6330256451291370204103987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33761367740220641088554597 6330256451291370204103987)
                ·
                  refine ⟨9495384676937055306155981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330256451291370204103987 9495384676937055306155981)
                  ·
                    refine ⟨3560769253851395739808493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9495384676937055306155981 3560769253851395739808493)
                    ·
                      refine ⟨1335288470194273402428185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560769253851395739808493 1335288470194273402428185)
                      ·
                        rfl

theorem cell23_2600465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_2600465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600465 prefixEnd_2600465 := by exact prefixLift 2600465
  have htrace : WordTrace (prefixWord ++ tailWord_2600465) baseStart_2600465 baseEnd_2600465 := by
    simpa [prefixWord, tailWord_2600465, baseEnd_2600465] using wordTrace_append hprefix tailTrace_2600465
  have hstable : (prefixWord ++ tailWord_2600465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600465).length < 2 ^ (prefixWord ++ tailWord_2600465).sum := by decide
  have hdescent : baseEnd_2600465 < baseStart_2600465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600469 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_2600469 : Nat := 118140960795 + 2600469 * 2 ^ 59
def prefixEnd_2600469 : Nat := 4983230072969 + 3 ^ 40 * 2600469 * 2
def baseEnd_2600469 : Nat := 1335290524116891386778167

theorem tailTrace_2600469 : CollatzResearch.WordTrace tailWord_2600469 prefixEnd_2600469 1335290524116891386778167 := by
  unfold tailWord_2600469
  simp only [CollatzResearch.WordTrace]
  refine ⟨94846896415952412591732461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63231264277301608394488307 94846896415952412591732461)
  ·
    refine ⟨35567586155982154721899673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94846896415952412591732461 35567586155982154721899673)
    ·
      refine ⟨26675689616986616041424755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35567586155982154721899673 26675689616986616041424755)
      ·
        refine ⟨40013534425479924062137133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26675689616986616041424755 40013534425479924062137133)
        ·
          refine ⟨15005075409554971523301425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40013534425479924062137133 15005075409554971523301425)
          ·
            refine ⟨11253806557166228642476069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15005075409554971523301425 11253806557166228642476069)
            ·
              refine ⟨2110088729468667870464263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11253806557166228642476069 2110088729468667870464263)
              ·
                refine ⟨3165133094203001805696395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110088729468667870464263 3165133094203001805696395)
                ·
                  refine ⟨4747699641304502708544593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165133094203001805696395 4747699641304502708544593)
                  ·
                    refine ⟨3560774730978377031408445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4747699641304502708544593 3560774730978377031408445)
                    ·
                      refine ⟨1335290524116891386778167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560774730978377031408445 1335290524116891386778167)
                      ·
                        rfl

theorem cell23_2600469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_2600469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600469 prefixEnd_2600469 := by exact prefixLift 2600469
  have htrace : WordTrace (prefixWord ++ tailWord_2600469) baseStart_2600469 baseEnd_2600469 := by
    simpa [prefixWord, tailWord_2600469, baseEnd_2600469] using wordTrace_append hprefix tailTrace_2600469
  have hstable : (prefixWord ++ tailWord_2600469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600469).length < 2 ^ (prefixWord ++ tailWord_2600469).sum := by decide
  have hdescent : baseEnd_2600469 < baseStart_2600469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600522 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_2600522 : Nat := 118140960795 + 2600522 * 2 ^ 59
def prefixEnd_2600522 : Nat := 4983230072969 + 3 ^ 40 * 2600522 * 2
def baseEnd_2600522 : Nat := 1335317738591579679415423

theorem tailTrace_2600522 : CollatzResearch.WordTrace tailWord_2600522 prefixEnd_2600522 1335317738591579679415423 := by
  unfold tailWord_2600522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23712207371190100660852955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63232552989840268428941213 23712207371190100660852955)
  ·
    refine ⟨35568311056785150991279433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23712207371190100660852955 35568311056785150991279433)
    ·
      refine ⟨26676233292588863243459575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35568311056785150991279433 26676233292588863243459575)
      ·
        refine ⟨40014349938883294865189363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26676233292588863243459575 40014349938883294865189363)
        ·
          refine ⟨60021524908324942297784045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40014349938883294865189363 60021524908324942297784045)
          ·
            refine ⟨22508071840621853361669017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60021524908324942297784045 22508071840621853361669017)
            ·
              refine ⟨16881053880466390021251763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22508071840621853361669017 16881053880466390021251763)
              ·
                refine ⟨25321580820699585031877645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16881053880466390021251763 25321580820699585031877645)
                ·
                  refine ⟨9495592807762344386954117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25321580820699585031877645 9495592807762344386954117)
                  ·
                    refine ⟨1780423651455439572553897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9495592807762344386954117 1780423651455439572553897)
                    ·
                      refine ⟨1335317738591579679415423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780423651455439572553897 1335317738591579679415423)
                      ·
                        rfl

theorem cell23_2600522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_2600522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600522 prefixEnd_2600522 := by exact prefixLift 2600522
  have htrace : WordTrace (prefixWord ++ tailWord_2600522) baseStart_2600522 baseEnd_2600522 := by
    simpa [prefixWord, tailWord_2600522, baseEnd_2600522] using wordTrace_append hprefix tailTrace_2600522
  have hstable : (prefixWord ++ tailWord_2600522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600522).length < 2 ^ (prefixWord ++ tailWord_2600522).sum := by decide
  have hdescent : baseEnd_2600522 < baseStart_2600522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600534 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2600534 : Nat := 118140960795 + 2600534 * 2 ^ 59
def prefixEnd_2600534 : Nat := 4983230072969 + 3 ^ 40 * 2600534 * 2
def baseEnd_2600534 : Nat := 1335323900359433632465369

theorem tailTrace_2600534 : CollatzResearch.WordTrace tailWord_2600534 prefixEnd_2600534 1335323900359433632465369 := by
  unfold tailWord_2600534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5928079197544808043303041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63232844773811285795232437 5928079197544808043303041)
  ·
    refine ⟨4446059398158606032477281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5928079197544808043303041 4446059398158606032477281)
    ·
      refine ⟨3334544548618954524357961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4446059398158606032477281 3334544548618954524357961)
      ·
        refine ⟨2500908411464215893268471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3334544548618954524357961 2500908411464215893268471)
        ·
          refine ⟨3751362617196323839902707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500908411464215893268471 3751362617196323839902707)
          ·
            refine ⟨5627043925794485759854061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751362617196323839902707 5627043925794485759854061)
            ·
              refine ⟨2110141472172932159945273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5627043925794485759854061 2110141472172932159945273)
              ·
                refine ⟨1582606104129699119958955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110141472172932159945273 1582606104129699119958955)
                ·
                  refine ⟨2373909156194548679938433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582606104129699119958955 2373909156194548679938433)
                  ·
                    refine ⟨1780431867145911509953825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373909156194548679938433 1780431867145911509953825)
                    ·
                      refine ⟨1335323900359433632465369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780431867145911509953825 1335323900359433632465369)
                      ·
                        rfl

theorem cell23_2600534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2600534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600534 prefixEnd_2600534 := by exact prefixLift 2600534
  have htrace : WordTrace (prefixWord ++ tailWord_2600534) baseStart_2600534 baseEnd_2600534 := by
    simpa [prefixWord, tailWord_2600534, baseEnd_2600534] using wordTrace_append hprefix tailTrace_2600534
  have hstable : (prefixWord ++ tailWord_2600534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600534).length < 2 ^ (prefixWord ++ tailWord_2600534).sum := by decide
  have hdescent : baseEnd_2600534 < baseStart_2600534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600555 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 3]
def baseStart_2600555 : Nat := 118140960795 + 2600555 * 2 ^ 59
def prefixEnd_2600555 : Nat := 4983230072969 + 3 ^ 40 * 2600555 * 2
def baseEnd_2600555 : Nat := 1335334683453178050302771

theorem tailTrace_2600555 : CollatzResearch.WordTrace tailWord_2600555 prefixEnd_2600555 1335334683453178050302771 := by
  unfold tailWord_2600555
  simp only [CollatzResearch.WordTrace]
  refine ⟨94850033093640849279363119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63233355395760566186242079 94850033093640849279363119)
  ·
    refine ⟨142275049640461273919044679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94850033093640849279363119 142275049640461273919044679)
    ·
      refine ⟨213412574460691910878567019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142275049640461273919044679 213412574460691910878567019)
      ·
        refine ⟨320118861691037866317850529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213412574460691910878567019 320118861691037866317850529)
        ·
          refine ⟨240089146268278399738387897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320118861691037866317850529 240089146268278399738387897)
          ·
            refine ⟨180066859701208799803790923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240089146268278399738387897 180066859701208799803790923)
            ·
              refine ⟨270100289551813199705686385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180066859701208799803790923 270100289551813199705686385)
              ·
                refine ⟨202575217163859899779264789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270100289551813199705686385 202575217163859899779264789)
                ·
                  refine ⟨9495713304555932802153037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 202575217163859899779264789 9495713304555932802153037)
                  ·
                    refine ⟨3560892489208474800807389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9495713304555932802153037 3560892489208474800807389)
                    ·
                      refine ⟨1335334683453178050302771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3560892489208474800807389 1335334683453178050302771)
                      ·
                        rfl

theorem cell23_2600555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 3].length) (baseStart_2600555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600555 prefixEnd_2600555 := by exact prefixLift 2600555
  have htrace : WordTrace (prefixWord ++ tailWord_2600555) baseStart_2600555 baseEnd_2600555 := by
    simpa [prefixWord, tailWord_2600555, baseEnd_2600555] using wordTrace_append hprefix tailTrace_2600555
  have hstable : (prefixWord ++ tailWord_2600555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600555).length < 2 ^ (prefixWord ++ tailWord_2600555).sum := by decide
  have hdescent : baseEnd_2600555 < baseStart_2600555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600585 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_2600585 : Nat := 118140960795 + 2600585 * 2 ^ 59
def prefixEnd_2600585 : Nat := 4983230072969 + 3 ^ 40 * 2600585 * 2
def baseEnd_2600585 : Nat := 1335350087872812932927633

theorem tailTrace_2600585 : CollatzResearch.WordTrace tailWord_2600585 prefixEnd_2600585 1335350087872812932927633 := by
  unfold tailWord_2600585
  simp only [CollatzResearch.WordTrace]
  refine ⟨94851127283532164402955209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63234084855688109601970139 94851127283532164402955209)
  ·
    refine ⟨71138345462649123302216407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94851127283532164402955209 71138345462649123302216407)
    ·
      refine ⟨106707518193973684953324611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71138345462649123302216407 106707518193973684953324611)
      ·
        refine ⟨160061277290960527429986917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106707518193973684953324611 160061277290960527429986917)
        ·
          refine ⟨30011489492055098893122547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160061277290960527429986917 30011489492055098893122547)
          ·
            refine ⟨45017234238082648339683821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30011489492055098893122547 45017234238082648339683821)
            ·
              refine ⟨16881462839280993127381433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45017234238082648339683821 16881462839280993127381433)
              ·
                refine ⟨12661097129460744845536075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16881462839280993127381433 12661097129460744845536075)
                ·
                  refine ⟨18991645694191117268304113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661097129460744845536075 18991645694191117268304113)
                  ·
                    refine ⟨14243734270643337951228085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18991645694191117268304113 14243734270643337951228085)
                    ·
                      refine ⟨1335350087872812932927633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14243734270643337951228085 1335350087872812932927633)
                      ·
                        rfl

theorem cell23_2600585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_2600585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600585 prefixEnd_2600585 := by exact prefixLift 2600585
  have htrace : WordTrace (prefixWord ++ tailWord_2600585) baseStart_2600585 baseEnd_2600585 := by
    simpa [prefixWord, tailWord_2600585, baseEnd_2600585] using wordTrace_append hprefix tailTrace_2600585
  have hstable : (prefixWord ++ tailWord_2600585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600585).length < 2 ^ (prefixWord ++ tailWord_2600585).sum := by decide
  have hdescent : baseEnd_2600585 < baseStart_2600585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600596 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 5]
def baseStart_2600596 : Nat := 118140960795 + 2600596 * 2 ^ 59
def prefixEnd_2600596 : Nat := 4983230072969 + 3 ^ 40 * 2600596 * 2
def baseEnd_2600596 : Nat := 148372859573334709987787

theorem tailTrace_2600596 : CollatzResearch.WordTrace tailWord_2600596 prefixEnd_2600596 148372859573334709987787 := by
  unfold tailWord_2600596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47425764243246156640802821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63234352324328208854403761 47425764243246156640802821)
  ·
    refine ⟨8892330795608654370150529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47425764243246156640802821 8892330795608654370150529)
    ·
      refine ⟨6669248096706490777612897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8892330795608654370150529 6669248096706490777612897)
      ·
        refine ⟨5001936072529868083209673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6669248096706490777612897 5001936072529868083209673)
        ·
          refine ⟨3751452054397401062407255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5001936072529868083209673 3751452054397401062407255)
          ·
            refine ⟨5627178081596101593610883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751452054397401062407255 5627178081596101593610883)
            ·
              refine ⟨8440767122394152390416325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5627178081596101593610883 8440767122394152390416325)
              ·
                refine ⟨1582643835448903573203061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8440767122394152390416325 1582643835448903573203061)
                ·
                  refine ⟨148372859573334709987787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582643835448903573203061 148372859573334709987787)
                  ·
                    rfl

theorem cell23_2600596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_2600596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600596 prefixEnd_2600596 := by exact prefixLift 2600596
  have htrace : WordTrace (prefixWord ++ tailWord_2600596) baseStart_2600596 baseEnd_2600596 := by
    simpa [prefixWord, tailWord_2600596, baseEnd_2600596] using wordTrace_append hprefix tailTrace_2600596
  have hstable : (prefixWord ++ tailWord_2600596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600596).length < 2 ^ (prefixWord ++ tailWord_2600596).sum := by decide
  have hdescent : baseEnd_2600596 < baseStart_2600596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600605 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2600605 : Nat := 118140960795 + 2600605 * 2 ^ 59
def prefixEnd_2600605 : Nat := 4983230072969 + 3 ^ 40 * 2600605 * 2
def baseEnd_2600605 : Nat := 445120119161967618225847

theorem tailTrace_2600605 : CollatzResearch.WordTrace tailWord_2600605 prefixEnd_2600605 445120119161967618225847 := by
  unfold tailWord_2600605
  simp only [CollatzResearch.WordTrace]
  refine ⟨94851856743459707818683269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63234571162306471879122179 94851856743459707818683269)
  ·
    refine ⟨17784723139398695216003113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94851856743459707818683269 17784723139398695216003113)
    ·
      refine ⟨13338542354549021412002335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17784723139398695216003113 13338542354549021412002335)
      ·
        refine ⟨20007813531823532118003503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13338542354549021412002335 20007813531823532118003503)
        ·
          refine ⟨30011720297735298177005255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20007813531823532118003503 30011720297735298177005255)
          ·
            refine ⟨45017580446602947265507883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30011720297735298177005255 45017580446602947265507883)
            ·
              refine ⟨67526370669904420898261825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45017580446602947265507883 67526370669904420898261825)
              ·
                refine ⟨50644778002428315673696369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67526370669904420898261825 50644778002428315673696369)
                ·
                  refine ⟨37983583501821236755272277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50644778002428315673696369 37983583501821236755272277)
                  ·
                    refine ⟨445120119161967618225847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37983583501821236755272277 445120119161967618225847)
                    ·
                      rfl

theorem cell23_2600605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2600605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600605 prefixEnd_2600605 := by exact prefixLift 2600605
  have htrace : WordTrace (prefixWord ++ tailWord_2600605) baseStart_2600605 baseEnd_2600605 := by
    simpa [prefixWord, tailWord_2600605, baseEnd_2600605] using wordTrace_append hprefix tailTrace_2600605
  have hstable : (prefixWord ++ tailWord_2600605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600605).length < 2 ^ (prefixWord ++ tailWord_2600605).sum := by decide
  have hdescent : baseEnd_2600605 < baseStart_2600605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600629 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2600629 : Nat := 118140960795 + 2600629 * 2 ^ 59
def prefixEnd_2600629 : Nat := 4983230072969 + 3 ^ 40 * 2600629 * 2
def baseEnd_2600629 : Nat := 1335372681021610760777431

theorem tailTrace_2600629 : CollatzResearch.WordTrace tailWord_2600629 prefixEnd_2600629 1335372681021610760777431 := by
  unfold tailWord_2600629
  simp only [CollatzResearch.WordTrace]
  refine ⟨94852732095372759917556941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63235154730248506611704627 94852732095372759917556941)
  ·
    refine ⟨35569774535764784969083853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94852732095372759917556941 35569774535764784969083853)
    ·
      refine ⟨13338665450911794363406445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35569774535764784969083853 13338665450911794363406445)
      ·
        refine ⟨5001999544091922886277417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13338665450911794363406445 5001999544091922886277417)
        ·
          refine ⟨3751499658068942164708063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5001999544091922886277417 3751499658068942164708063)
          ·
            refine ⟨5627249487103413247062095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751499658068942164708063 5627249487103413247062095)
            ·
              refine ⟨8440874230655119870593143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5627249487103413247062095 8440874230655119870593143)
              ·
                refine ⟨12661311345982679805889715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8440874230655119870593143 12661311345982679805889715)
                ·
                  refine ⟨18991967018974019708834573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661311345982679805889715 18991967018974019708834573)
                  ·
                    refine ⟨7121987632115257390812965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18991967018974019708834573 7121987632115257390812965)
                    ·
                      refine ⟨1335372681021610760777431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7121987632115257390812965 1335372681021610760777431)
                      ·
                        rfl

theorem cell23_2600629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2600629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600629 prefixEnd_2600629 := by exact prefixLift 2600629
  have htrace : WordTrace (prefixWord ++ tailWord_2600629) baseStart_2600629 baseEnd_2600629 := by
    simpa [prefixWord, tailWord_2600629, baseEnd_2600629] using wordTrace_append hprefix tailTrace_2600629
  have hstable : (prefixWord ++ tailWord_2600629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600629).length < 2 ^ (prefixWord ++ tailWord_2600629).sum := by decide
  have hdescent : baseEnd_2600629 < baseStart_2600629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600682 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2600682 : Nat := 118140960795 + 2600682 * 2 ^ 59
def prefixEnd_2600682 : Nat := 4983230072969 + 3 ^ 40 * 2600682 * 2
def baseEnd_2600682 : Nat := 445133298498766351138229

theorem tailTrace_2600682 : CollatzResearch.WordTrace tailWord_2600682 prefixEnd_2600682 445133298498766351138229 := by
  unfold tailWord_2600682
  simp only [CollatzResearch.WordTrace]
  refine ⟨23713666291045187492309075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63236443442787166646157533 23713666291045187492309075)
  ·
    refine ⟨35570499436567781238463613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23713666291045187492309075 35570499436567781238463613)
    ·
      refine ⟨13338937288712917964423855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35570499436567781238463613 13338937288712917964423855)
      ·
        refine ⟨20008405933069376946635783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13338937288712917964423855 20008405933069376946635783)
        ·
          refine ⟨30012608899604065419953675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20008405933069376946635783 30012608899604065419953675)
          ·
            refine ⟨45018913349406098129930513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30012608899604065419953675 45018913349406098129930513)
            ·
              refine ⟨33764185012054573597447885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45018913349406098129930513 33764185012054573597447885)
              ·
                refine ⟨12661569379520465099042957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33764185012054573597447885 12661569379520465099042957)
                ·
                  refine ⟨4748088517320174412141109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12661569379520465099042957 4748088517320174412141109)
                  ·
                    refine ⟨445133298498766351138229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4748088517320174412141109 445133298498766351138229)
                    ·
                      rfl

theorem cell23_2600682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2600682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600682 prefixEnd_2600682 := by exact prefixLift 2600682
  have htrace : WordTrace (prefixWord ++ tailWord_2600682) baseStart_2600682 baseEnd_2600682 := by
    simpa [prefixWord, tailWord_2600682, baseEnd_2600682] using wordTrace_append hprefix tailTrace_2600682
  have hstable : (prefixWord ++ tailWord_2600682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600682).length < 2 ^ (prefixWord ++ tailWord_2600682).sum := by decide
  have hdescent : baseEnd_2600682 < baseStart_2600682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600689 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 1, 5, 2]
def baseStart_2600689 : Nat := 118140960795 + 2600689 * 2 ^ 59
def prefixEnd_2600689 : Nat := 4983230072969 + 3 ^ 40 * 2600689 * 2
def baseEnd_2600689 : Nat := 1335403489860880526027155

theorem tailTrace_2600689 : CollatzResearch.WordTrace tailWord_2600689 prefixEnd_2600689 1335403489860880526027155 := by
  unfold tailWord_2600689
  simp only [CollatzResearch.WordTrace]
  refine ⟨94854920475155390164741121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63236613650103593443160747 94854920475155390164741121)
  ·
    refine ⟨71141190356366542623555841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94854920475155390164741121 71141190356366542623555841)
    ·
      refine ⟨53355892767274906967666881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71141190356366542623555841 53355892767274906967666881)
      ·
        refine ⟨40016919575456180225750161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53355892767274906967666881 40016919575456180225750161)
        ·
          refine ⟨30012689681592135169312621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40016919575456180225750161 30012689681592135169312621)
          ·
            refine ⟨11254758630597050688492233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30012689681592135169312621 11254758630597050688492233)
            ·
              refine ⟨8441068972947788016369175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11254758630597050688492233 8441068972947788016369175)
              ·
                refine ⟨12661603459421682024553763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8441068972947788016369175 12661603459421682024553763)
                ·
                  refine ⟨18992405189132523036830645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661603459421682024553763 18992405189132523036830645)
                  ·
                    refine ⟨1780537986481174034702873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18992405189132523036830645 1780537986481174034702873)
                    ·
                      refine ⟨1335403489860880526027155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780537986481174034702873 1335403489860880526027155)
                      ·
                        rfl

theorem cell23_2600689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_2600689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600689 prefixEnd_2600689 := by exact prefixLift 2600689
  have htrace : WordTrace (prefixWord ++ tailWord_2600689) baseStart_2600689 baseEnd_2600689 := by
    simpa [prefixWord, tailWord_2600689, baseEnd_2600689] using wordTrace_append hprefix tailTrace_2600689
  have hstable : (prefixWord ++ tailWord_2600689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600689).length < 2 ^ (prefixWord ++ tailWord_2600689).sum := by decide
  have hdescent : baseEnd_2600689 < baseStart_2600689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600696 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 1, 1, 3]
def baseStart_2600696 : Nat := 118140960795 + 2600696 * 2 ^ 59
def prefixEnd_2600696 : Nat := 4983230072969 + 3 ^ 40 * 2600696 * 2
def baseEnd_2600696 : Nat := 1335407084225461998639623

theorem tailTrace_2600696 : CollatzResearch.WordTrace tailWord_2600696 prefixEnd_2600696 1335407084225461998639623 := by
  unfold tailWord_2600696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47427587893065015180122971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63236783857420020240163961 47427587893065015180122971)
  ·
    refine ⟨71141381839597522770184457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47427587893065015180122971 71141381839597522770184457)
    ·
      refine ⟨53356036379698142077638343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71141381839597522770184457 53356036379698142077638343)
      ·
        refine ⟨80034054569547213116457515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53356036379698142077638343 80034054569547213116457515)
        ·
          refine ⟨120051081854320819674686273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80034054569547213116457515 120051081854320819674686273)
          ·
            refine ⟨90038311390740614756014705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120051081854320819674686273 90038311390740614756014705)
            ·
              refine ⟨67528733543055461067011029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90038311390740614756014705 67528733543055461067011029)
              ·
                refine ⟨1582704692415362368758071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67528733543055461067011029 1582704692415362368758071)
                ·
                  refine ⟨2374057038623043553137107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582704692415362368758071 2374057038623043553137107)
                  ·
                    refine ⟨3561085557934565329705661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2374057038623043553137107 3561085557934565329705661)
                    ·
                      refine ⟨1335407084225461998639623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3561085557934565329705661 1335407084225461998639623)
                      ·
                        rfl

theorem cell23_2600696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_2600696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600696 prefixEnd_2600696 := by exact prefixLift 2600696
  have htrace : WordTrace (prefixWord ++ tailWord_2600696) baseStart_2600696 baseEnd_2600696 := by
    simpa [prefixWord, tailWord_2600696, baseEnd_2600696] using wordTrace_append hprefix tailTrace_2600696
  have hstable : (prefixWord ++ tailWord_2600696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600696).length < 2 ^ (prefixWord ++ tailWord_2600696).sum := by decide
  have hdescent : baseEnd_2600696 < baseStart_2600696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600732 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2600732 : Nat := 118140960795 + 2600732 * 2 ^ 59
def prefixEnd_2600732 : Nat := 4983230072969 + 3 ^ 40 * 2600732 * 2
def baseEnd_2600732 : Nat := 1335425569529023857789457

theorem tailTrace_2600732 : CollatzResearch.WordTrace tailWord_2600732 prefixEnd_2600732 1335425569529023857789457 := by
  unfold tailWord_2600732
  simp only [CollatzResearch.WordTrace]
  refine ⟨47428244406999804254278225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63237659209333072339037633 47428244406999804254278225)
  ·
    refine ⟨35571183305249853190708669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47428244406999804254278225 35571183305249853190708669)
    ·
      refine ⟨13339193739468694946515751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35571183305249853190708669 13339193739468694946515751)
      ·
        refine ⟨20008790609203042419773627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13339193739468694946515751 20008790609203042419773627)
        ·
          refine ⟨30013185913804563629660441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20008790609203042419773627 30013185913804563629660441)
          ·
            refine ⟨22509889435353422722245331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30013185913804563629660441 22509889435353422722245331)
            ·
              refine ⟨33764834153030134083367997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22509889435353422722245331 33764834153030134083367997)
              ·
                refine ⟨12661812807386300281262999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33764834153030134083367997 12661812807386300281262999)
                ·
                  refine ⟨18992719211079450421894499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661812807386300281262999 18992719211079450421894499)
                  ·
                    refine ⟨28489078816619175632841749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18992719211079450421894499 28489078816619175632841749)
                    ·
                      refine ⟨1335425569529023857789457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28489078816619175632841749 1335425569529023857789457)
                      ·
                        rfl

theorem cell23_2600732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2600732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600732 prefixEnd_2600732 := by exact prefixLift 2600732
  have htrace : WordTrace (prefixWord ++ tailWord_2600732) baseStart_2600732 baseEnd_2600732 := by
    simpa [prefixWord, tailWord_2600732, baseEnd_2600732] using wordTrace_append hprefix tailTrace_2600732
  have hstable : (prefixWord ++ tailWord_2600732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600732).length < 2 ^ (prefixWord ++ tailWord_2600732).sum := by decide
  have hdescent : baseEnd_2600732 < baseStart_2600732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600736 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 5, 2, 2]
def baseStart_2600736 : Nat := 118140960795 + 2600736 * 2 ^ 59
def prefixEnd_2600736 : Nat := 4983230072969 + 3 ^ 40 * 2600736 * 2
def baseEnd_2600736 : Nat := 1335427623451641842139439

theorem tailTrace_2600736 : CollatzResearch.WordTrace tailWord_2600736 prefixEnd_2600736 1335427623451641842139439 := by
  unfold tailWord_2600736
  simp only [CollatzResearch.WordTrace]
  refine ⟨47428317352992558595851031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63237756470656744794468041 47428317352992558595851031)
  ·
    refine ⟨71142476029488837893776547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47428317352992558595851031 71142476029488837893776547)
    ·
      refine ⟨106713714044233256840664821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71142476029488837893776547 106713714044233256840664821)
      ·
        refine ⟨10004410691646867828812327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106713714044233256840664821 10004410691646867828812327)
        ·
          refine ⟨15006616037470301743218491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004410691646867828812327 15006616037470301743218491)
          ·
            refine ⟨22509924056205452614827737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15006616037470301743218491 22509924056205452614827737)
            ·
              refine ⟨16882443042154089461120803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22509924056205452614827737 16882443042154089461120803)
              ·
                refine ⟨25323664563231134191681205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16882443042154089461120803 25323664563231134191681205)
                ·
                  refine ⟨2374093552802918830470113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25323664563231134191681205 2374093552802918830470113)
                  ·
                    refine ⟨1780570164602189122852585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2374093552802918830470113 1780570164602189122852585)
                    ·
                      refine ⟨1335427623451641842139439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780570164602189122852585 1335427623451641842139439)
                      ·
                        rfl

theorem cell23_2600736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_2600736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600736 prefixEnd_2600736 := by exact prefixLift 2600736
  have htrace : WordTrace (prefixWord ++ tailWord_2600736) baseStart_2600736 baseEnd_2600736 := by
    simpa [prefixWord, tailWord_2600736, baseEnd_2600736] using wordTrace_append hprefix tailTrace_2600736
  have hstable : (prefixWord ++ tailWord_2600736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600736).length < 2 ^ (prefixWord ++ tailWord_2600736).sum := by decide
  have hdescent : baseEnd_2600736 < baseStart_2600736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600756 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2600756 : Nat := 118140960795 + 2600756 * 2 ^ 59
def prefixEnd_2600756 : Nat := 4983230072969 + 3 ^ 40 * 2600756 * 2
def baseEnd_2600756 : Nat := 1335437893064731763889347

theorem tailTrace_2600756 : CollatzResearch.WordTrace tailWord_2600756 prefixEnd_2600756 1335437893064731763889347 := by
  unfold tailWord_2600756
  simp only [CollatzResearch.WordTrace]
  refine ⟨47428682082956330303715061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63238242777275107071620081 47428682082956330303715061)
  ·
    refine ⟨4446438945277155965973287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47428682082956330303715061 4446438945277155965973287)
    ·
      refine ⟨6669658417915733948959931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446438945277155965973287 6669658417915733948959931)
      ·
        refine ⟨10004487626873600923439897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6669658417915733948959931 10004487626873600923439897)
        ·
          refine ⟨7503365720155200692579923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10004487626873600923439897 7503365720155200692579923)
          ·
            refine ⟨11255048580232801038869885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7503365720155200692579923 11255048580232801038869885)
            ·
              refine ⟨4220643217587300389576207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11255048580232801038869885 4220643217587300389576207)
              ·
                refine ⟨6330964826380950584364311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220643217587300389576207 6330964826380950584364311)
                ·
                  refine ⟨9496447239571425876546467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330964826380950584364311 9496447239571425876546467)
                  ·
                    refine ⟨14244670859357138814819701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9496447239571425876546467 14244670859357138814819701)
                    ·
                      refine ⟨1335437893064731763889347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14244670859357138814819701 1335437893064731763889347)
                      ·
                        rfl

theorem cell23_2600756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2600756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600756 prefixEnd_2600756 := by exact prefixLift 2600756
  have htrace : WordTrace (prefixWord ++ tailWord_2600756) baseStart_2600756 baseEnd_2600756 := by
    simpa [prefixWord, tailWord_2600756, baseEnd_2600756] using wordTrace_append hprefix tailTrace_2600756
  have hstable : (prefixWord ++ tailWord_2600756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600756).length < 2 ^ (prefixWord ++ tailWord_2600756).sum := by decide
  have hdescent : baseEnd_2600756 < baseStart_2600756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600782 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2600782 : Nat := 118140960795 + 2600782 * 2 ^ 59
def prefixEnd_2600782 : Nat := 4983230072969 + 3 ^ 40 * 2600782 * 2
def baseEnd_2600782 : Nat := 1335451243561748662164227

theorem tailTrace_2600782 : CollatzResearch.WordTrace tailWord_2600782 prefixEnd_2600782 1335451243561748662164227 := by
  unfold tailWord_2600782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11857289057977308380984575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63238874975878978031917733 11857289057977308380984575)
  ·
    refine ⟨17785933586965962571476863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11857289057977308380984575 17785933586965962571476863)
    ·
      refine ⟨26678900380448943857215295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17785933586965962571476863 26678900380448943857215295)
      ·
        refine ⟨40018350570673415785822943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26678900380448943857215295 40018350570673415785822943)
        ·
          refine ⟨60027525856010123678734415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40018350570673415785822943 60027525856010123678734415)
          ·
            refine ⟨90041288784015185518101623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60027525856010123678734415 90041288784015185518101623)
            ·
              refine ⟨135061933176022778277152435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90041288784015185518101623 135061933176022778277152435)
              ·
                refine ⟨202592899764034167415728653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135061933176022778277152435 202592899764034167415728653)
                ·
                  refine ⟨75972337411512812780898245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202592899764034167415728653 75972337411512812780898245)
                  ·
                    refine ⟨14244813264658652396418421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75972337411512812780898245 14244813264658652396418421)
                    ·
                      refine ⟨1335451243561748662164227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14244813264658652396418421 1335451243561748662164227)
                      ·
                        rfl

theorem cell23_2600782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2600782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600782 prefixEnd_2600782 := by exact prefixLift 2600782
  have htrace : WordTrace (prefixWord ++ tailWord_2600782) baseStart_2600782 baseEnd_2600782 := by
    simpa [prefixWord, tailWord_2600782, baseEnd_2600782] using wordTrace_append hprefix tailTrace_2600782
  have hstable : (prefixWord ++ tailWord_2600782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600782).length < 2 ^ (prefixWord ++ tailWord_2600782).sum := by decide
  have hdescent : baseEnd_2600782 < baseStart_2600782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600786 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2600786 : Nat := 118140960795 + 2600786 * 2 ^ 59
def prefixEnd_2600786 : Nat := 4983230072969 + 3 ^ 40 * 2600786 * 2
def baseEnd_2600786 : Nat := 1335453297484366646514209

theorem tailTrace_2600786 : CollatzResearch.WordTrace tailWord_2600786 prefixEnd_2600786 1335453297484366646514209 := by
  unfold tailWord_2600786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23714614588950993932755553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63238972237202650487348141 23714614588950993932755553)
  ·
    refine ⟨17785960941713245449566665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23714614588950993932755553 17785960941713245449566665)
    ·
      refine ⟨13339470706284934087174999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17785960941713245449566665 13339470706284934087174999)
      ·
        refine ⟨20009206059427401130762499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13339470706284934087174999 20009206059427401130762499)
        ·
          refine ⟨30013809089141101696143749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20009206059427401130762499 30013809089141101696143749)
          ·
            refine ⟨5627589204213956568026953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30013809089141101696143749 5627589204213956568026953)
            ·
              refine ⟨4220691903160467426020215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627589204213956568026953 4220691903160467426020215)
              ·
                refine ⟨6331037854740701139030323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220691903160467426020215 6331037854740701139030323)
                ·
                  refine ⟨9496556782111051708545485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6331037854740701139030323 9496556782111051708545485)
                  ·
                    refine ⟨3561208793291644390704557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9496556782111051708545485 3561208793291644390704557)
                    ·
                      refine ⟨1335453297484366646514209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3561208793291644390704557 1335453297484366646514209)
                      ·
                        rfl

theorem cell23_2600786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2600786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600786 prefixEnd_2600786 := by exact prefixLift 2600786
  have htrace : WordTrace (prefixWord ++ tailWord_2600786) baseStart_2600786 baseEnd_2600786 := by
    simpa [prefixWord, tailWord_2600786, baseEnd_2600786] using wordTrace_append hprefix tailTrace_2600786
  have hstable : (prefixWord ++ tailWord_2600786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600786).length < 2 ^ (prefixWord ++ tailWord_2600786).sum := by decide
  have hdescent : baseEnd_2600786 < baseStart_2600786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600879 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 2, 5]
def baseStart_2600879 : Nat := 118140960795 + 2600879 * 2 ^ 59
def prefixEnd_2600879 : Nat := 4983230072969 + 3 ^ 40 * 2600879 * 2
def baseEnd_2600879 : Nat := 445167017061744927550427

theorem tailTrace_2600879 : CollatzResearch.WordTrace tailWord_2600879 prefixEnd_2600879 445167017061744927550427 := by
  unfold tailWord_2600879
  simp only [CollatzResearch.WordTrace]
  refine ⟨94861850344467052614157691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63241233562978035076105127 94861850344467052614157691)
  ·
    refine ⟨142292775516700578921236537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94861850344467052614157691 142292775516700578921236537)
    ·
      refine ⟨106719581637525434190927403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142292775516700578921236537 106719581637525434190927403)
      ·
        refine ⟨160079372456288151286391105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106719581637525434190927403 160079372456288151286391105)
        ·
          refine ⟨120059529342216113464793329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160079372456288151286391105 120059529342216113464793329)
          ·
            refine ⟨90044647006662085098594997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120059529342216113464793329 90044647006662085098594997)
            ·
              refine ⟨8441685656874570477993281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90044647006662085098594997 8441685656874570477993281)
              ·
                refine ⟨6331264242655927858494961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8441685656874570477993281 6331264242655927858494961)
                ·
                  refine ⟨4748448181991945893871221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6331264242655927858494961 4748448181991945893871221)
                  ·
                    refine ⟨445167017061744927550427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4748448181991945893871221 445167017061744927550427)
                    ·
                      rfl

theorem cell23_2600879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_2600879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600879 prefixEnd_2600879 := by exact prefixLift 2600879
  have htrace : WordTrace (prefixWord ++ tailWord_2600879) baseStart_2600879 baseEnd_2600879 := by
    simpa [prefixWord, tailWord_2600879, baseEnd_2600879] using wordTrace_append hprefix tailTrace_2600879
  have hstable : (prefixWord ++ tailWord_2600879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600879).length < 2 ^ (prefixWord ++ tailWord_2600879).sum := by decide
  have hdescent : baseEnd_2600879 < baseStart_2600879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600889 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2600889 : Nat := 118140960795 + 2600889 * 2 ^ 59
def prefixEnd_2600889 : Nat := 4983230072969 + 3 ^ 40 * 2600889 * 2
def baseEnd_2600889 : Nat := 1335506185991779743526235

theorem tailTrace_2600889 : CollatzResearch.WordTrace tailWord_2600889 prefixEnd_2600889 1335506185991779743526235 := by
  unfold tailWord_2600889
  simp only [CollatzResearch.WordTrace]
  refine ⟨94862215074430824322021721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63241476716287216214681147 94862215074430824322021721)
  ·
    refine ⟨71146661305823118241516291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94862215074430824322021721 71146661305823118241516291)
    ·
      refine ⟨106719991958734677362274437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71146661305823118241516291 106719991958734677362274437)
      ·
        refine ⟨20009998492262752005426457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106719991958734677362274437 20009998492262752005426457)
        ·
          refine ⟨15007498869197064004069843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20009998492262752005426457 15007498869197064004069843)
          ·
            refine ⟨22511248303795596006104765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15007498869197064004069843 22511248303795596006104765)
            ·
              refine ⟨8441718113923348502289287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22511248303795596006104765 8441718113923348502289287)
              ·
                refine ⟨12662577170885022753433931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8441718113923348502289287 12662577170885022753433931)
                ·
                  refine ⟨18993865756327534130150897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12662577170885022753433931 18993865756327534130150897)
                  ·
                    refine ⟨14245399317245650597613173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18993865756327534130150897 14245399317245650597613173)
                    ·
                      refine ⟨1335506185991779743526235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14245399317245650597613173 1335506185991779743526235)
                      ·
                        rfl

theorem cell23_2600889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2600889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600889 prefixEnd_2600889 := by exact prefixLift 2600889
  have htrace : WordTrace (prefixWord ++ tailWord_2600889) baseStart_2600889 baseEnd_2600889 := by
    simpa [prefixWord, tailWord_2600889, baseEnd_2600889] using wordTrace_append hprefix tailTrace_2600889
  have hstable : (prefixWord ++ tailWord_2600889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600889).length < 2 ^ (prefixWord ++ tailWord_2600889).sum := by decide
  have hdescent : baseEnd_2600889 < baseStart_2600889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600943 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 1, 4]
def baseStart_2600943 : Nat := 118140960795 + 2600943 * 2 ^ 59
def prefixEnd_2600943 : Nat := 4983230072969 + 3 ^ 40 * 2600943 * 2
def baseEnd_2600943 : Nat := 445177971315707510750329

theorem tailTrace_2600943 : CollatzResearch.WordTrace tailWord_2600943 prefixEnd_2600943 445177971315707510750329 := by
  unfold tailWord_2600943
  simp only [CollatzResearch.WordTrace]
  refine ⟨94864184616235191544487483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63242789744156794362991655 94864184616235191544487483)
  ·
    refine ⟨142296276924352787316731225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94864184616235191544487483 142296276924352787316731225)
    ·
      refine ⟨106722207693264590487548419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142296276924352787316731225 106722207693264590487548419)
      ·
        refine ⟨160083311539896885731322629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106722207693264590487548419 160083311539896885731322629)
        ·
          refine ⟨30015620913730666074622993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160083311539896885731322629 30015620913730666074622993)
          ·
            refine ⟨22511715685297999555967245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30015620913730666074622993 22511715685297999555967245)
            ·
              refine ⟨8441893381986749833487717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22511715685297999555967245 8441893381986749833487717)
              ·
                refine ⟨1582855009122515593778947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8441893381986749833487717 1582855009122515593778947)
                ·
                  refine ⟨2374282513683773390668421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582855009122515593778947 2374282513683773390668421)
                  ·
                    refine ⟨445177971315707510750329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2374282513683773390668421 445177971315707510750329)
                    ·
                      rfl

theorem cell23_2600943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 4].length) (baseStart_2600943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600943 prefixEnd_2600943 := by exact prefixLift 2600943
  have htrace : WordTrace (prefixWord ++ tailWord_2600943) baseStart_2600943 baseEnd_2600943 := by
    simpa [prefixWord, tailWord_2600943, baseEnd_2600943] using wordTrace_append hprefix tailTrace_2600943
  have hstable : (prefixWord ++ tailWord_2600943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600943).length < 2 ^ (prefixWord ++ tailWord_2600943).sum := by decide
  have hdescent : baseEnd_2600943 < baseStart_2600943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600950 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2600950 : Nat := 118140960795 + 2600950 * 2 ^ 59
def prefixEnd_2600950 : Nat := 4983230072969 + 3 ^ 40 * 2600950 * 2
def baseEnd_2600950 : Nat := 1335537508311704004863455

theorem tailTrace_2600950 : CollatzResearch.WordTrace tailWord_2600950 prefixEnd_2600950 1335537508311704004863455 := by
  unfold tailWord_2600950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929027495450614483749519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63242959951473221159994869 5929027495450614483749519)
  ·
    refine ⟨8893541243175921725624279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5929027495450614483749519 8893541243175921725624279)
    ·
      refine ⟨13340311864763882588436419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8893541243175921725624279 13340311864763882588436419)
      ·
        refine ⟨20010467797145823882654629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13340311864763882588436419 20010467797145823882654629)
        ·
          refine ⟨3751962711964841977997743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20010467797145823882654629 3751962711964841977997743)
          ·
            refine ⟨5627944067947262966996615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751962711964841977997743 5627944067947262966996615)
            ·
              refine ⟨8441916101920894450494923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5627944067947262966996615 8441916101920894450494923)
              ·
                refine ⟨12662874152881341675742385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8441916101920894450494923 12662874152881341675742385)
                ·
                  refine ⟨9497155614661006256806789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12662874152881341675742385 9497155614661006256806789)
                  ·
                    refine ⟨1780716677748938673151273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9497155614661006256806789 1780716677748938673151273)
                    ·
                      refine ⟨1335537508311704004863455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780716677748938673151273 1335537508311704004863455)
                      ·
                        rfl

theorem cell23_2600950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2600950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600950 prefixEnd_2600950 := by exact prefixLift 2600950
  have htrace : WordTrace (prefixWord ++ tailWord_2600950) baseStart_2600950 baseEnd_2600950 := by
    simpa [prefixWord, tailWord_2600950, baseEnd_2600950] using wordTrace_append hprefix tailTrace_2600950
  have hstable : (prefixWord ++ tailWord_2600950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600950).length < 2 ^ (prefixWord ++ tailWord_2600950).sum := by decide
  have hdescent : baseEnd_2600950 < baseStart_2600950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600970 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_2600970 : Nat := 118140960795 + 2600970 * 2 ^ 59
def prefixEnd_2600970 : Nat := 4983230072969 + 3 ^ 40 * 2600970 * 2
def baseEnd_2600970 : Nat := 1335547777924793926613363

theorem tailTrace_2600970 : CollatzResearch.WordTrace tailWord_2600970 prefixEnd_2600970 1335547777924793926613363 := by
  unfold tailWord_2600970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23716292346784343788930091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63243446258091583437146909 23716292346784343788930091)
  ·
    refine ⟨35574438520176515683395137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23716292346784343788930091 35574438520176515683395137)
    ·
      refine ⟨26680828890132386762546353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35574438520176515683395137 26680828890132386762546353)
      ·
        refine ⟨20010621667599290071909765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26680828890132386762546353 20010621667599290071909765)
        ·
          refine ⟨3751991562674866888483081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20010621667599290071909765 3751991562674866888483081)
          ·
            refine ⟨2813993672006150166362311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3751991562674866888483081 2813993672006150166362311)
            ·
              refine ⟨4220990508009225249543467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813993672006150166362311 4220990508009225249543467)
              ·
                refine ⟨6331485762013837874315201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220990508009225249543467 6331485762013837874315201)
                ·
                  refine ⟨4748614321510378405736401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6331485762013837874315201 4748614321510378405736401)
                  ·
                    refine ⟨3561460741132783804302301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4748614321510378405736401 3561460741132783804302301)
                    ·
                      refine ⟨1335547777924793926613363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3561460741132783804302301 1335547777924793926613363)
                      ·
                        rfl

theorem cell23_2600970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_2600970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600970 prefixEnd_2600970 := by exact prefixLift 2600970
  have htrace : WordTrace (prefixWord ++ tailWord_2600970) baseStart_2600970 baseEnd_2600970 := by
    simpa [prefixWord, tailWord_2600970, baseEnd_2600970] using wordTrace_append hprefix tailTrace_2600970
  have hstable : (prefixWord ++ tailWord_2600970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600970).length < 2 ^ (prefixWord ++ tailWord_2600970).sum := by decide
  have hdescent : baseEnd_2600970 < baseStart_2600970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600976 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 1, 5, 2]
def baseStart_2600976 : Nat := 118140960795 + 2600976 * 2 ^ 59
def prefixEnd_2600976 : Nat := 4983230072969 + 3 ^ 40 * 2600976 * 2
def baseEnd_2600976 : Nat := 1335550858808720903138335

theorem tailTrace_2600976 : CollatzResearch.WordTrace tailWord_2600976 prefixEnd_2600976 1335550858808720903138335 := by
  unfold tailWord_2600976
  simp only [CollatzResearch.WordTrace]
  refine ⟨47432694112557819090219391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63243592150077092120292521 47432694112557819090219391)
  ·
    refine ⟨71149041168836728635329087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47432694112557819090219391 71149041168836728635329087)
    ·
      refine ⟨106723561753255092952993631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71149041168836728635329087 106723561753255092952993631)
      ·
        refine ⟨160085342629882639429490447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106723561753255092952993631 160085342629882639429490447)
        ·
          refine ⟨240128013944823959144235671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160085342629882639429490447 240128013944823959144235671)
          ·
            refine ⟨360192020917235938716353507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240128013944823959144235671 360192020917235938716353507)
            ·
              refine ⟨540288031375853908074530261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360192020917235938716353507 540288031375853908074530261)
              ·
                refine ⟨12663000735371575970496803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 540288031375853908074530261 12663000735371575970496803)
                ·
                  refine ⟨18994501103057363955745205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12663000735371575970496803 18994501103057363955745205)
                  ·
                    refine ⟨1780734478411627870851113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18994501103057363955745205 1780734478411627870851113)
                    ·
                      refine ⟨1335550858808720903138335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780734478411627870851113 1335550858808720903138335)
                      ·
                        rfl

theorem cell23_2600976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 5, 2].length) (baseStart_2600976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2600976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2600976 prefixEnd_2600976 := by exact prefixLift 2600976
  have htrace : WordTrace (prefixWord ++ tailWord_2600976) baseStart_2600976 baseEnd_2600976 := by
    simpa [prefixWord, tailWord_2600976, baseEnd_2600976] using wordTrace_append hprefix tailTrace_2600976
  have hstable : (prefixWord ++ tailWord_2600976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600976).length < 2 ^ (prefixWord ++ tailWord_2600976).sum := by decide
  have hdescent : baseEnd_2600976 < baseStart_2600976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601019 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6]
def baseStart_2601019 : Nat := 118140960795 + 2601019 * 2 ^ 59
def prefixEnd_2601019 : Nat := 4983230072969 + 3 ^ 40 * 2601019 * 2
def baseEnd_2601019 : Nat := 1335572938476864234900637

theorem tailTrace_2601019 : CollatzResearch.WordTrace tailWord_2601019 prefixEnd_2601019 1335572938476864234900637 := by
  unfold tailWord_2601019
  simp only [CollatzResearch.WordTrace]
  refine ⟨94866956563959856524254111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63244637709306571016169407 94866956563959856524254111)
  ·
    refine ⟨142300434845939784786381167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94866956563959856524254111 142300434845939784786381167)
    ·
      refine ⟨213450652268909677179571751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142300434845939784786381167 213450652268909677179571751)
      ·
        refine ⟨320175978403364515769357627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213450652268909677179571751 320175978403364515769357627)
        ·
          refine ⟨480263967605046773654036441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320175978403364515769357627 480263967605046773654036441)
          ·
            refine ⟨360197975703785080240527331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480263967605046773654036441 360197975703785080240527331)
            ·
              refine ⟨540296963555677620360790997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360197975703785080240527331 540296963555677620360790997)
              ·
                refine ⟨12663210083336194227206039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 540296963555677620360790997 12663210083336194227206039)
                ·
                  refine ⟨18994815125004291340809059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12663210083336194227206039 18994815125004291340809059)
                  ·
                    refine ⟨28492222687506437011213589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18994815125004291340809059 28492222687506437011213589)
                    ·
                      refine ⟨1335572938476864234900637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28492222687506437011213589 1335572938476864234900637)
                      ·
                        rfl

theorem cell23_2601019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_2601019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601019 prefixEnd_2601019 := by exact prefixLift 2601019
  have htrace : WordTrace (prefixWord ++ tailWord_2601019) baseStart_2601019 baseEnd_2601019 := by
    simpa [prefixWord, tailWord_2601019, baseEnd_2601019] using wordTrace_append hprefix tailTrace_2601019
  have hstable : (prefixWord ++ tailWord_2601019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601019).length < 2 ^ (prefixWord ++ tailWord_2601019).sum := by decide
  have hdescent : baseEnd_2601019 < baseStart_2601019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601036 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2601036 : Nat := 118140960795 + 2601036 * 2 ^ 59
def prefixEnd_2601036 : Nat := 4983230072969 + 3 ^ 40 * 2601036 * 2
def baseEnd_2601036 : Nat := 1335581667647990668388059

theorem tailTrace_2601036 : CollatzResearch.WordTrace tailWord_2601036 prefixEnd_2601036 1335581667647990668388059 := by
  unfold tailWord_2601036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47433788302449134213811481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63245051069932178951748641 47433788302449134213811481)
  ·
    refine ⟨35575341226836850660358611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47433788302449134213811481 35575341226836850660358611)
    ·
      refine ⟨53363011840255275990537917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35575341226836850660358611 53363011840255275990537917)
      ·
        refine ⟨20011129440095728496451719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53363011840255275990537917 20011129440095728496451719)
        ·
          refine ⟨30016694160143592744677579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20011129440095728496451719 30016694160143592744677579)
          ·
            refine ⟨45025041240215389117016369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30016694160143592744677579 45025041240215389117016369)
            ·
              refine ⟨33768780930161541837762277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45025041240215389117016369 33768780930161541837762277)
              ·
                refine ⟨6331646424405289094580427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33768780930161541837762277 6331646424405289094580427)
                ·
                  refine ⟨9497469636607933641870641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6331646424405289094580427 9497469636607933641870641)
                  ·
                    refine ⟨7123102227455950231402981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9497469636607933641870641 7123102227455950231402981)
                    ·
                      refine ⟨1335581667647990668388059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7123102227455950231402981 1335581667647990668388059)
                      ·
                        rfl

theorem cell23_2601036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2601036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601036 prefixEnd_2601036 := by exact prefixLift 2601036
  have htrace : WordTrace (prefixWord ++ tailWord_2601036) baseStart_2601036 baseEnd_2601036 := by
    simpa [prefixWord, tailWord_2601036, baseEnd_2601036] using wordTrace_append hprefix tailTrace_2601036
  have hstable : (prefixWord ++ tailWord_2601036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601036).length < 2 ^ (prefixWord ++ tailWord_2601036).sum := by decide
  have hdescent : baseEnd_2601036 < baseStart_2601036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601053 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2601053 : Nat := 118140960795 + 2601053 * 2 ^ 59
def prefixEnd_2601053 : Nat := 4983230072969 + 3 ^ 40 * 2601053 * 2
def baseEnd_2601053 : Nat := 1335590396819117101875481

theorem tailTrace_2601053 : CollatzResearch.WordTrace tailWord_2601053 prefixEnd_2601053 1335590396819117101875481 := by
  unfold tailWord_2601053
  simp only [CollatzResearch.WordTrace]
  refine ⟨94868196645836680330991813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63245464430557786887327875 94868196645836680330991813)
  ·
    refine ⟨17787786871094377562060965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94868196645836680330991813 17787786871094377562060965)
    ·
      refine ⟨3335210038330195792886431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17787786871094377562060965 3335210038330195792886431)
      ·
        refine ⟨5002815057495293689329647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3335210038330195792886431 5002815057495293689329647)
        ·
          refine ⟨7504222586242940533994471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5002815057495293689329647 7504222586242940533994471)
          ·
            refine ⟨11256333879364410800991707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7504222586242940533994471 11256333879364410800991707)
            ·
              refine ⟨16884500819046616201487561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11256333879364410800991707 16884500819046616201487561)
              ·
                refine ⟨12663375614284962151115671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16884500819046616201487561 12663375614284962151115671)
                ·
                  refine ⟨18995063421427443226673507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12663375614284962151115671 18995063421427443226673507)
                  ·
                    refine ⟨28492595132141164840010261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18995063421427443226673507 28492595132141164840010261)
                    ·
                      refine ⟨1335590396819117101875481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28492595132141164840010261 1335590396819117101875481)
                      ·
                        rfl

theorem cell23_2601053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2601053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601053 prefixEnd_2601053 := by exact prefixLift 2601053
  have htrace : WordTrace (prefixWord ++ tailWord_2601053) baseStart_2601053 baseEnd_2601053 := by
    simpa [prefixWord, tailWord_2601053, baseEnd_2601053] using wordTrace_append hprefix tailTrace_2601053
  have hstable : (prefixWord ++ tailWord_2601053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601053).length < 2 ^ (prefixWord ++ tailWord_2601053).sum := by decide
  have hdescent : baseEnd_2601053 < baseStart_2601053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601164 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2601164 : Nat := 118140960795 + 2601164 * 2 ^ 59
def prefixEnd_2601164 : Nat := 4983230072969 + 3 ^ 40 * 2601164 * 2
def baseEnd_2601164 : Nat := 1335647393171766167587471

theorem tailTrace_2601164 : CollatzResearch.WordTrace tailWord_2601164 prefixEnd_2601164 1335647393171766167587471 := by
  unfold tailWord_2601164
  simp only [CollatzResearch.WordTrace]
  refine ⟨47436122574217273144141273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63248163432289697525521697 47436122574217273144141273)
  ·
    refine ⟨35577091930662954858105955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47436122574217273144141273 35577091930662954858105955)
    ·
      refine ⟨53365637895994432287158933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35577091930662954858105955 53365637895994432287158933)
      ·
        refine ⟨2501514276374739013460575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53365637895994432287158933 2501514276374739013460575)
        ·
          refine ⟨3752271414562108520190863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501514276374739013460575 3752271414562108520190863)
          ·
            refine ⟨5628407121843162780286295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752271414562108520190863 5628407121843162780286295)
            ·
              refine ⟨8442610682764744170429443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5628407121843162780286295 8442610682764744170429443)
              ·
                refine ⟨12663916024147116255644165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8442610682764744170429443 12663916024147116255644165)
                ·
                  refine ⟨2374484254527584297933281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12663916024147116255644165 2374484254527584297933281)
                  ·
                    refine ⟨1780863190895688223449961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2374484254527584297933281 1780863190895688223449961)
                    ·
                      refine ⟨1335647393171766167587471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780863190895688223449961 1335647393171766167587471)
                      ·
                        rfl

theorem cell23_2601164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2601164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601164 prefixEnd_2601164 := by exact prefixLift 2601164
  have htrace : WordTrace (prefixWord ++ tailWord_2601164) baseStart_2601164 baseEnd_2601164 := by
    simpa [prefixWord, tailWord_2601164, baseEnd_2601164] using wordTrace_append hprefix tailTrace_2601164
  have hstable : (prefixWord ++ tailWord_2601164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601164).length < 2 ^ (prefixWord ++ tailWord_2601164).sum := by decide
  have hdescent : baseEnd_2601164 < baseStart_2601164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601170 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_2601170 : Nat := 118140960795 + 2601170 * 2 ^ 59
def prefixEnd_2601170 : Nat := 4983230072969 + 3 ^ 40 * 2601170 * 2
def baseEnd_2601170 : Nat := 148405608228410349345827

theorem tailTrace_2601170 : CollatzResearch.WordTrace tailWord_2601170 prefixEnd_2601170 148405608228410349345827 := by
  unfold tailWord_2601170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23718115996603202328250241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63248309324275206208667309 23718115996603202328250241)
  ·
    refine ⟨17788586997452401746187681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23718115996603202328250241 17788586997452401746187681)
    ·
      refine ⟨13341440248089301309640761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17788586997452401746187681 13341440248089301309640761)
      ·
        refine ⟨10006080186066975982230571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13341440248089301309640761 10006080186066975982230571)
        ·
          refine ⟨15009120279100463973345857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006080186066975982230571 15009120279100463973345857)
          ·
            refine ⟨11256840209325347980009393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15009120279100463973345857 11256840209325347980009393)
            ·
              refine ⟨8442630156994010985007045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11256840209325347980009393 8442630156994010985007045)
              ·
                refine ⟨1582993154436377059688821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8442630156994010985007045 1582993154436377059688821)
                ·
                  refine ⟨148405608228410349345827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582993154436377059688821 148405608228410349345827)
                  ·
                    rfl

theorem cell23_2601170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_2601170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601170 prefixEnd_2601170 := by exact prefixLift 2601170
  have htrace : WordTrace (prefixWord ++ tailWord_2601170) baseStart_2601170 baseEnd_2601170 := by
    simpa [prefixWord, tailWord_2601170, baseEnd_2601170] using wordTrace_append hprefix tailTrace_2601170
  have hstable : (prefixWord ++ tailWord_2601170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601170).length < 2 ^ (prefixWord ++ tailWord_2601170).sum := by decide
  have hdescent : baseEnd_2601170 < baseStart_2601170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601181 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2601181 : Nat := 118140960795 + 2601181 * 2 ^ 59
def prefixEnd_2601181 : Nat := 4983230072969 + 3 ^ 40 * 2601181 * 2
def baseEnd_2601181 : Nat := 1335656122342892601074893

theorem tailTrace_2601181 : CollatzResearch.WordTrace tailWord_2601181 prefixEnd_2601181 1335656122342892601074893 := by
  unfold tailWord_2601181
  simp only [CollatzResearch.WordTrace]
  refine ⟨94872865189372958191651397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63248576792915305461100931 94872865189372958191651397)
  ·
    refine ⟨17788662223007429660934637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94872865189372958191651397 17788662223007429660934637)
    ·
      refine ⟨6670748333627786122850489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17788662223007429660934637 6670748333627786122850489)
      ·
        refine ⟨5003061250220839592137867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6670748333627786122850489 5003061250220839592137867)
        ·
          refine ⟨7504591875331259388206801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5003061250220839592137867 7504591875331259388206801)
          ·
            refine ⟨5628443906498444541155101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7504591875331259388206801 5628443906498444541155101)
            ·
              refine ⟨2110666464936916702933163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5628443906498444541155101 2110666464936916702933163)
              ·
                refine ⟨3165999697405375054399745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110666464936916702933163 3165999697405375054399745)
                ·
                  refine ⟨2374499773054031290799809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165999697405375054399745 2374499773054031290799809)
                  ·
                    refine ⟨1780874829790523468099857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2374499773054031290799809 1780874829790523468099857)
                    ·
                      refine ⟨1335656122342892601074893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780874829790523468099857 1335656122342892601074893)
                      ·
                        rfl

theorem cell23_2601181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2601181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601181 prefixEnd_2601181 := by exact prefixLift 2601181
  have htrace : WordTrace (prefixWord ++ tailWord_2601181) baseStart_2601181 baseEnd_2601181 := by
    simpa [prefixWord, tailWord_2601181, baseEnd_2601181] using wordTrace_append hprefix tailTrace_2601181
  have hstable : (prefixWord ++ tailWord_2601181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601181).length < 2 ^ (prefixWord ++ tailWord_2601181).sum := by decide
  have hdescent : baseEnd_2601181 < baseStart_2601181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601196 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_2601196 : Nat := 118140960795 + 2601196 * 2 ^ 59
def prefixEnd_2601196 : Nat := 4983230072969 + 3 ^ 40 * 2601196 * 2
def baseEnd_2601196 : Nat := 445221274850903347462441

theorem tailTrace_2601196 : CollatzResearch.WordTrace tailWord_2601196 prefixEnd_2601196 445221274850903347462441 := by
  unfold tailWord_2601196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47436706142159307876723721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63248941522879077168964961 47436706142159307876723721)
  ·
    refine ⟨35577529606619480907542791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47436706142159307876723721 35577529606619480907542791)
    ·
      refine ⟨53366294409929221361314187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35577529606619480907542791 53366294409929221361314187)
      ·
        refine ⟨80049441614893832041971281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53366294409929221361314187 80049441614893832041971281)
        ·
          refine ⟨60037081211170374031478461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80049441614893832041971281 60037081211170374031478461)
          ·
            refine ⟨22513905454188890261804423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60037081211170374031478461 22513905454188890261804423)
            ·
              refine ⟨33770858181283335392706635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22513905454188890261804423 33770858181283335392706635)
              ·
                refine ⟨50656287271925003089059953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33770858181283335392706635 50656287271925003089059953)
                ·
                  refine ⟨37992215453943752316794965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50656287271925003089059953 37992215453943752316794965)
                  ·
                    refine ⟨445221274850903347462441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37992215453943752316794965 445221274850903347462441)
                    ·
                      rfl

theorem cell23_2601196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_2601196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601196 prefixEnd_2601196 := by exact prefixLift 2601196
  have htrace : WordTrace (prefixWord ++ tailWord_2601196) baseStart_2601196 baseEnd_2601196 := by
    simpa [prefixWord, tailWord_2601196, baseEnd_2601196] using wordTrace_append hprefix tailTrace_2601196
  have hstable : (prefixWord ++ tailWord_2601196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601196).length < 2 ^ (prefixWord ++ tailWord_2601196).sum := by decide
  have hdescent : baseEnd_2601196 < baseStart_2601196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601203 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 4]
def baseStart_2601203 : Nat := 118140960795 + 2601203 * 2 ^ 59
def prefixEnd_2601203 : Nat := 4983230072969 + 3 ^ 40 * 2601203 * 2
def baseEnd_2601203 : Nat := 1335667418917291514999791

theorem tailTrace_2601203 : CollatzResearch.WordTrace tailWord_2601203 prefixEnd_2601203 1335667418917291514999791 := by
  unfold tailWord_2601203
  simp only [CollatzResearch.WordTrace]
  refine ⟨94873667595293255948952263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63249111730195503965968175 94873667595293255948952263)
  ·
    refine ⟨142310501392939883923428395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94873667595293255948952263 142310501392939883923428395)
    ·
      refine ⟨213465752089409825885142593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142310501392939883923428395 213465752089409825885142593)
      ·
        refine ⟨160099314067057369413856945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213465752089409825885142593 160099314067057369413856945)
        ·
          refine ⟨120074485550293027060392709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160099314067057369413856945 120074485550293027060392709)
          ·
            refine ⟨22513966040679942573823633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120074485550293027060392709 22513966040679942573823633)
            ·
              refine ⟨16885474530509956930367725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22513966040679942573823633 16885474530509956930367725)
              ·
                refine ⟨6332052948941233848887897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16885474530509956930367725 6332052948941233848887897)
                ·
                  refine ⟨4749039711705925386665923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332052948941233848887897 4749039711705925386665923)
                  ·
                    refine ⟨7123559567558888079998885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4749039711705925386665923 7123559567558888079998885)
                    ·
                      refine ⟨1335667418917291514999791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7123559567558888079998885 1335667418917291514999791)
                      ·
                        rfl

theorem cell23_2601203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_2601203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601203 prefixEnd_2601203 := by exact prefixLift 2601203
  have htrace : WordTrace (prefixWord ++ tailWord_2601203) baseStart_2601203 baseEnd_2601203 := by
    simpa [prefixWord, tailWord_2601203, baseEnd_2601203] using wordTrace_append hprefix tailTrace_2601203
  have hstable : (prefixWord ++ tailWord_2601203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601203).length < 2 ^ (prefixWord ++ tailWord_2601203).sum := by decide
  have hdescent : baseEnd_2601203 < baseStart_2601203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601213 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_2601213 : Nat := 118140960795 + 2601213 * 2 ^ 59
def prefixEnd_2601213 : Nat := 4983230072969 + 3 ^ 40 * 2601213 * 2
def baseEnd_2601213 : Nat := 445224184574612158624915

theorem tailTrace_2601213 : CollatzResearch.WordTrace tailWord_2601213 prefixEnd_2601213 445224184574612158624915 := by
  unfold tailWord_2601213
  simp only [CollatzResearch.WordTrace]
  refine ⟨94874032325257027656816293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63249354883504685104544195 94874032325257027656816293)
  ·
    refine ⟨17788881060985692685653055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94874032325257027656816293 17788881060985692685653055)
    ·
      refine ⟨26683321591478539028479583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17788881060985692685653055 26683321591478539028479583)
      ·
        refine ⟨40024982387217808542719375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26683321591478539028479583 40024982387217808542719375)
        ·
          refine ⟨60037473580826712814079063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40024982387217808542719375 60037473580826712814079063)
          ·
            refine ⟨90056210371240069221118595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60037473580826712814079063 90056210371240069221118595)
            ·
              refine ⟨135084315556860103831677893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90056210371240069221118595 135084315556860103831677893)
              ·
                refine ⟨25328309166911269468439605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135084315556860103831677893 25328309166911269468439605)
                ·
                  refine ⟨2374528984397931512666213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25328309166911269468439605 2374528984397931512666213)
                  ·
                    refine ⟨445224184574612158624915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2374528984397931512666213 445224184574612158624915)
                    ·
                      rfl

theorem cell23_2601213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_2601213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601213 prefixEnd_2601213 := by exact prefixLift 2601213
  have htrace : WordTrace (prefixWord ++ tailWord_2601213) baseStart_2601213 baseEnd_2601213 := by
    simpa [prefixWord, tailWord_2601213, baseEnd_2601213] using wordTrace_append hprefix tailTrace_2601213
  have hstable : (prefixWord ++ tailWord_2601213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601213).length < 2 ^ (prefixWord ++ tailWord_2601213).sum := by decide
  have hdescent : baseEnd_2601213 < baseStart_2601213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601216 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2601216 : Nat := 118140960795 + 2601216 * 2 ^ 59
def prefixEnd_2601216 : Nat := 4983230072969 + 3 ^ 40 * 2601216 * 2
def baseEnd_2601216 : Nat := 1335674094165799964137231

theorem tailTrace_2601216 : CollatzResearch.WordTrace tailWord_2601216 prefixEnd_2601216 1335674094165799964137231 := by
  unfold tailWord_2601216
  simp only [CollatzResearch.WordTrace]
  refine ⟨47437070872123079584587751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63249427829497439446117001 47437070872123079584587751)
  ·
    refine ⟨71155606308184619376881627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47437070872123079584587751 71155606308184619376881627)
    ·
      refine ⟨106733409462276929065322441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71155606308184619376881627 106733409462276929065322441)
      ·
        refine ⟨80050057096707696798991831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106733409462276929065322441 80050057096707696798991831)
        ·
          refine ⟨120075085645061545198487747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80050057096707696798991831 120075085645061545198487747)
          ·
            refine ⟨180112628467592317797731621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120075085645061545198487747 180112628467592317797731621)
            ·
              refine ⟨33771117837673559587074679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180112628467592317797731621 33771117837673559587074679)
              ·
                refine ⟨50656676756510339380612019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33771117837673559587074679 50656676756510339380612019)
                ·
                  refine ⟨75985015134765509070918029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50656676756510339380612019 75985015134765509070918029)
                  ·
                    refine ⟨28494380675537065901594261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75985015134765509070918029 28494380675537065901594261)
                    ·
                      refine ⟨1335674094165799964137231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28494380675537065901594261 1335674094165799964137231)
                      ·
                        rfl

theorem cell23_2601216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2601216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601216 prefixEnd_2601216 := by exact prefixLift 2601216
  have htrace : WordTrace (prefixWord ++ tailWord_2601216) baseStart_2601216 baseEnd_2601216 := by
    simpa [prefixWord, tailWord_2601216, baseEnd_2601216] using wordTrace_append hprefix tailTrace_2601216
  have hstable : (prefixWord ++ tailWord_2601216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601216).length < 2 ^ (prefixWord ++ tailWord_2601216).sum := by decide
  have hdescent : baseEnd_2601216 < baseStart_2601216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601280 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 4, 3, 2]
def baseStart_2601280 : Nat := 118140960795 + 2601280 * 2 ^ 59
def prefixEnd_2601280 : Nat := 4983230072969 + 3 ^ 40 * 2601280 * 2
def baseEnd_2601280 : Nat := 1335706956927687713736937

theorem tailTrace_2601280 : CollatzResearch.WordTrace tailWord_2601280 prefixEnd_2601280 1335706956927687713736937 := by
  unfold tailWord_2601280
  simp only [CollatzResearch.WordTrace]
  refine ⟨47438238008007149049752647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63250984010676198733003529 47438238008007149049752647)
  ·
    refine ⟨71157357012010723574628971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47438238008007149049752647 71157357012010723574628971)
    ·
      refine ⟨106736035518016085361943457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71157357012010723574628971 106736035518016085361943457)
      ·
        refine ⟨80052026638512064021457593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106736035518016085361943457 80052026638512064021457593)
        ·
          refine ⟨60039019978884048016093195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80052026638512064021457593 60039019978884048016093195)
          ·
            refine ⟨90058529968326072024139793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60039019978884048016093195 90058529968326072024139793)
            ·
              refine ⟨67543897476244554018104845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90058529968326072024139793 67543897476244554018104845)
              ·
                refine ⟨25328961553591707756789317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67543897476244554018104845 25328961553591707756789317)
                ·
                  refine ⟨4749180291298445204397997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25328961553591707756789317 4749180291298445204397997)
                  ·
                    refine ⟨1780942609236916951649249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4749180291298445204397997 1780942609236916951649249)
                    ·
                      refine ⟨1335706956927687713736937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780942609236916951649249 1335706956927687713736937)
                      ·
                        rfl

theorem cell23_2601280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_2601280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601280 prefixEnd_2601280 := by exact prefixLift 2601280
  have htrace : WordTrace (prefixWord ++ tailWord_2601280) baseStart_2601280 baseEnd_2601280 := by
    simpa [prefixWord, tailWord_2601280, baseEnd_2601280] using wordTrace_append hprefix tailTrace_2601280
  have hstable : (prefixWord ++ tailWord_2601280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601280).length < 2 ^ (prefixWord ++ tailWord_2601280).sum := by decide
  have hdescent : baseEnd_2601280 < baseStart_2601280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601314 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_2601314 : Nat := 118140960795 + 2601314 * 2 ^ 59
def prefixEnd_2601314 : Nat := 4983230072969 + 3 ^ 40 * 2601314 * 2
def baseEnd_2601314 : Nat := 1335724415269940580711781

theorem tailTrace_2601314 : CollatzResearch.WordTrace tailWord_2601314 prefixEnd_2601314 1335724415269940580711781 := by
  unfold tailWord_2601314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23719429024472780476560749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63251810731927414604161997 23719429024472780476560749)
  ·
    refine ⟨8894785884177292678710281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23719429024472780476560749 8894785884177292678710281)
    ·
      refine ⟨6671089413132969509032711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8894785884177292678710281 6671089413132969509032711)
      ·
        refine ⟨10006634119699454263549067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6671089413132969509032711 10006634119699454263549067)
        ·
          refine ⟨15009951179549181395323601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006634119699454263549067 15009951179549181395323601)
          ·
            refine ⟨11257463384661886046492701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15009951179549181395323601 11257463384661886046492701)
            ·
              refine ⟨4221548769248207267434763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11257463384661886046492701 4221548769248207267434763)
              ·
                refine ⟨6332323153872310901152145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221548769248207267434763 6332323153872310901152145)
                ·
                  refine ⟨4749242365404233175864109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332323153872310901152145 4749242365404233175864109)
                  ·
                    refine ⟨1780965887026587440949041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4749242365404233175864109 1780965887026587440949041)
                    ·
                      refine ⟨1335724415269940580711781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1780965887026587440949041 1335724415269940580711781)
                      ·
                        rfl

theorem cell23_2601314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_2601314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601314 prefixEnd_2601314 := by exact prefixLift 2601314
  have htrace : WordTrace (prefixWord ++ tailWord_2601314) baseStart_2601314 baseEnd_2601314 := by
    simpa [prefixWord, tailWord_2601314, baseEnd_2601314] using wordTrace_append hprefix tailTrace_2601314
  have hstable : (prefixWord ++ tailWord_2601314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601314).length < 2 ^ (prefixWord ++ tailWord_2601314).sum := by decide
  have hdescent : baseEnd_2601314 < baseStart_2601314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
